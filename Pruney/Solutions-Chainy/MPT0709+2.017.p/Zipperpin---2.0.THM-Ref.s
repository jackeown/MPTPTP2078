%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hf2y7Y2Z7E

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:08 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 561 expanded)
%              Number of leaves         :   25 ( 214 expanded)
%              Depth                    :   27
%              Number of atoms          : 1127 (5117 expanded)
%              Number of equality atoms :   61 ( 309 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('1',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ X18 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('21',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k9_relat_1 @ X3 @ ( k9_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','19','39'])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('54',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) @ X0 ) )
      | ( X0
        = ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X1
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','63','64','65','66'])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('69',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','74'])).

thf('76',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) )
    | ( sk_A
      = ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('84',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('85',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('91',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k9_relat_1 @ X3 @ ( k9_relat_1 @ X4 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X17 ) @ X18 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k2_funct_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X1 @ X2 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X1 @ X2 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hf2y7Y2Z7E
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.89/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.09  % Solved by: fo/fo7.sh
% 0.89/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.09  % done 489 iterations in 0.633s
% 0.89/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.09  % SZS output start Refutation
% 0.89/1.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.09  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.09  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.89/1.09  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.89/1.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.09  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.09  thf(t61_funct_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.09       ( ( v2_funct_1 @ A ) =>
% 0.89/1.09         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.89/1.09             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.89/1.09           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.89/1.09             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.09  thf('0', plain,
% 0.89/1.09      (![X19 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X19)
% 0.89/1.09          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.89/1.09              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.89/1.09          | ~ (v1_funct_1 @ X19)
% 0.89/1.09          | ~ (v1_relat_1 @ X19))),
% 0.89/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.09  thf('1', plain,
% 0.89/1.09      (![X19 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X19)
% 0.89/1.09          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.89/1.09              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.89/1.09          | ~ (v1_funct_1 @ X19)
% 0.89/1.09          | ~ (v1_relat_1 @ X19))),
% 0.89/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.09  thf(fc3_funct_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.89/1.09       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.89/1.09  thf('2', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('3', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v1_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v2_funct_1 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['1', '2'])).
% 0.89/1.09  thf('4', plain,
% 0.89/1.09      (![X19 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X19)
% 0.89/1.09          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.89/1.09              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.89/1.09          | ~ (v1_funct_1 @ X19)
% 0.89/1.09          | ~ (v1_relat_1 @ X19))),
% 0.89/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.09  thf('5', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('6', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v2_funct_1 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['4', '5'])).
% 0.89/1.09  thf(t164_funct_1, conjecture,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.09       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.89/1.09         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.89/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.09    (~( ![A:$i,B:$i]:
% 0.89/1.09        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.09          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.89/1.09            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.89/1.09    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.89/1.09  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(t71_relat_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.09       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.09  thf('8', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.89/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.09  thf(t146_funct_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( v1_relat_1 @ B ) =>
% 0.89/1.09       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.89/1.09         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.89/1.09  thf('9', plain,
% 0.89/1.09      (![X15 : $i, X16 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.89/1.09          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)))
% 0.89/1.09          | ~ (v1_relat_1 @ X16))),
% 0.89/1.09      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.89/1.09  thf('10', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X1 @ X0)
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | (r1_tarski @ X1 @ 
% 0.89/1.09             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.09              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['8', '9'])).
% 0.89/1.09  thf('11', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('12', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X1 @ X0)
% 0.89/1.09          | (r1_tarski @ X1 @ 
% 0.89/1.09             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.09              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.89/1.09      inference('demod', [status(thm)], ['10', '11'])).
% 0.89/1.09  thf(t67_funct_1, axiom,
% 0.89/1.09    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.09  thf('13', plain,
% 0.89/1.09      (![X20 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.89/1.09  thf(t155_funct_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.09       ( ( v2_funct_1 @ B ) =>
% 0.89/1.09         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.89/1.09  thf('14', plain,
% 0.89/1.09      (![X17 : $i, X18 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X17)
% 0.89/1.09          | ((k10_relat_1 @ X17 @ X18)
% 0.89/1.09              = (k9_relat_1 @ (k2_funct_1 @ X17) @ X18))
% 0.89/1.09          | ~ (v1_funct_1 @ X17)
% 0.89/1.09          | ~ (v1_relat_1 @ X17))),
% 0.89/1.09      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.89/1.09  thf('15', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['13', '14'])).
% 0.89/1.09  thf('16', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('17', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf(fc4_funct_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.89/1.09       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.89/1.09  thf('18', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.89/1.09  thf('19', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.09  thf('20', plain,
% 0.89/1.09      (![X20 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.89/1.09  thf('21', plain,
% 0.89/1.09      (![X19 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X19)
% 0.89/1.09          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.89/1.09              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.89/1.09          | ~ (v1_funct_1 @ X19)
% 0.89/1.09          | ~ (v1_relat_1 @ X19))),
% 0.89/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.09  thf('22', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.09            = (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['20', '21'])).
% 0.89/1.09  thf('23', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.89/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.09  thf('24', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('25', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('26', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.89/1.09  thf('27', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.09           = (k6_relat_1 @ X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.89/1.09  thf('28', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.09  thf(t159_relat_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( v1_relat_1 @ B ) =>
% 0.89/1.09       ( ![C:$i]:
% 0.89/1.09         ( ( v1_relat_1 @ C ) =>
% 0.89/1.09           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.89/1.09             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.89/1.09  thf('29', plain,
% 0.89/1.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ X3)
% 0.89/1.09          | ((k9_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.89/1.09              = (k9_relat_1 @ X3 @ (k9_relat_1 @ X4 @ X5)))
% 0.89/1.09          | ~ (v1_relat_1 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.89/1.09  thf('30', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.09  thf('31', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k10_relat_1 @ (k6_relat_1 @ X1) @ (k9_relat_1 @ X2 @ X0))
% 0.89/1.09            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.89/1.09          | ~ (v1_relat_1 @ X2)
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['29', '30'])).
% 0.89/1.09  thf('32', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('33', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k10_relat_1 @ (k6_relat_1 @ X1) @ (k9_relat_1 @ X2 @ X0))
% 0.89/1.09            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.89/1.09          | ~ (v1_relat_1 @ X2))),
% 0.89/1.09      inference('demod', [status(thm)], ['31', '32'])).
% 0.89/1.09  thf('34', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k10_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.89/1.09            (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.09            = (k9_relat_1 @ 
% 0.89/1.09               (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)) @ X0))
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['28', '33'])).
% 0.89/1.09  thf('35', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('36', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.89/1.09           (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.09           = (k9_relat_1 @ 
% 0.89/1.09              (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)) @ X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.09  thf('37', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.09           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['27', '36'])).
% 0.89/1.09  thf('38', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.09  thf('39', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.09           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.09           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['37', '38'])).
% 0.89/1.09  thf('40', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X1 @ X0)
% 0.89/1.09          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.89/1.09      inference('demod', [status(thm)], ['12', '19', '39'])).
% 0.89/1.09  thf('41', plain,
% 0.89/1.09      ((r1_tarski @ sk_A @ 
% 0.89/1.09        (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['7', '40'])).
% 0.89/1.09  thf('42', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.09  thf(t145_funct_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.09       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.89/1.09  thf('43', plain,
% 0.89/1.09      (![X13 : $i, X14 : $i]:
% 0.89/1.09         ((r1_tarski @ (k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X14)) @ X14)
% 0.89/1.09          | ~ (v1_funct_1 @ X13)
% 0.89/1.09          | ~ (v1_relat_1 @ X13))),
% 0.89/1.09      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.89/1.09  thf('44', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((r1_tarski @ 
% 0.89/1.09           (k10_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.09            (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.89/1.09           X0)
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.09          | ~ (v1_funct_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['42', '43'])).
% 0.89/1.09  thf('45', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('46', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.89/1.09  thf('47', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (r1_tarski @ 
% 0.89/1.09          (k10_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.09           (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 0.89/1.09          X0)),
% 0.89/1.09      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.89/1.09  thf('48', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.09           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.09           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['37', '38'])).
% 0.89/1.09  thf('49', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 0.89/1.09      inference('demod', [status(thm)], ['47', '48'])).
% 0.89/1.09  thf(d10_xboole_0, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.09  thf('50', plain,
% 0.89/1.09      (![X0 : $i, X2 : $i]:
% 0.89/1.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.09  thf('51', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.09          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['49', '50'])).
% 0.89/1.09  thf('52', plain,
% 0.89/1.09      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['41', '51'])).
% 0.89/1.09  thf('53', plain,
% 0.89/1.09      (![X19 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X19)
% 0.89/1.09          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.89/1.09              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.89/1.09          | ~ (v1_funct_1 @ X19)
% 0.89/1.09          | ~ (v1_relat_1 @ X19))),
% 0.89/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.09  thf('54', plain,
% 0.89/1.09      (![X19 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X19)
% 0.89/1.09          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 0.89/1.09              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 0.89/1.09          | ~ (v1_funct_1 @ X19)
% 0.89/1.09          | ~ (v1_relat_1 @ X19))),
% 0.89/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.09  thf('55', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 0.89/1.09      inference('demod', [status(thm)], ['47', '48'])).
% 0.89/1.09  thf('56', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((r1_tarski @ 
% 0.89/1.09           (k10_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1) @ X1)
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v2_funct_1 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['54', '55'])).
% 0.89/1.09  thf('57', plain,
% 0.89/1.09      (![X0 : $i, X2 : $i]:
% 0.89/1.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.09  thf('58', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X1)
% 0.89/1.09          | ~ (v1_funct_1 @ X1)
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ~ (r1_tarski @ X0 @ 
% 0.89/1.09               (k10_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)) @ X0))
% 0.89/1.09          | ((X0) = (k10_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)) @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['56', '57'])).
% 0.89/1.09  thf('59', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X1 @ 
% 0.89/1.09             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v2_funct_1 @ X0)
% 0.89/1.09          | ((X1) = (k10_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1))
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v2_funct_1 @ X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['53', '58'])).
% 0.89/1.09  thf('60', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((X1) = (k10_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1))
% 0.89/1.09          | ~ (v2_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (r1_tarski @ X1 @ 
% 0.89/1.09               (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['59'])).
% 0.89/1.09  thf('61', plain,
% 0.89/1.09      ((~ (r1_tarski @ sk_A @ sk_A)
% 0.89/1.09        | ~ (v1_relat_1 @ sk_B)
% 0.89/1.09        | ~ (v1_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v2_funct_1 @ sk_B)
% 0.89/1.09        | ((sk_A)
% 0.89/1.09            = (k10_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['52', '60'])).
% 0.89/1.09  thf('62', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.09  thf('63', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.09      inference('simplify', [status(thm)], ['62'])).
% 0.89/1.09  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('66', plain, ((v2_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('67', plain,
% 0.89/1.09      (((sk_A)
% 0.89/1.09         = (k10_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['61', '63', '64', '65', '66'])).
% 0.89/1.09  thf('68', plain,
% 0.89/1.09      (![X13 : $i, X14 : $i]:
% 0.89/1.09         ((r1_tarski @ (k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X14)) @ X14)
% 0.89/1.09          | ~ (v1_funct_1 @ X13)
% 0.89/1.09          | ~ (v1_relat_1 @ X13))),
% 0.89/1.09      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.89/1.09  thf('69', plain,
% 0.89/1.09      (((r1_tarski @ 
% 0.89/1.09         (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ sk_A)
% 0.89/1.09        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 0.89/1.09        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['67', '68'])).
% 0.89/1.09  thf('70', plain,
% 0.89/1.09      ((~ (v2_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v1_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v1_relat_1 @ sk_B)
% 0.89/1.09        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 0.89/1.09        | (r1_tarski @ 
% 0.89/1.09           (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ 
% 0.89/1.09           sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['6', '69'])).
% 0.89/1.09  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('74', plain,
% 0.89/1.09      ((~ (v1_funct_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 0.89/1.09        | (r1_tarski @ 
% 0.89/1.09           (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ 
% 0.89/1.09           sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.89/1.09  thf('75', plain,
% 0.89/1.09      ((~ (v2_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v1_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v1_relat_1 @ sk_B)
% 0.89/1.09        | (r1_tarski @ 
% 0.89/1.09           (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ 
% 0.89/1.09           sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['3', '74'])).
% 0.89/1.09  thf('76', plain, ((v2_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('77', plain, ((v1_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('79', plain,
% 0.89/1.09      ((r1_tarski @ 
% 0.89/1.09        (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A) @ sk_A)),
% 0.89/1.09      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.89/1.09  thf('80', plain,
% 0.89/1.09      (![X0 : $i, X2 : $i]:
% 0.89/1.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.09  thf('81', plain,
% 0.89/1.09      ((~ (r1_tarski @ sk_A @ 
% 0.89/1.09           (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))
% 0.89/1.09        | ((sk_A)
% 0.89/1.09            = (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['79', '80'])).
% 0.89/1.09  thf('82', plain,
% 0.89/1.09      ((~ (r1_tarski @ sk_A @ 
% 0.89/1.09           (k9_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))
% 0.89/1.09        | ~ (v1_relat_1 @ sk_B)
% 0.89/1.09        | ~ (v1_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v2_funct_1 @ sk_B)
% 0.89/1.09        | ((sk_A)
% 0.89/1.09            = (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['0', '81'])).
% 0.89/1.09  thf('83', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.89/1.09           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.09  thf('84', plain,
% 0.89/1.09      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['41', '51'])).
% 0.89/1.09  thf('85', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.09      inference('simplify', [status(thm)], ['62'])).
% 0.89/1.09  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('87', plain, ((v1_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('88', plain, ((v2_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('89', plain,
% 0.89/1.09      (((sk_A)
% 0.89/1.09         = (k9_relat_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)],
% 0.89/1.09                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.89/1.09  thf(dt_k2_funct_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.09       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.89/1.09         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.89/1.09  thf('90', plain,
% 0.89/1.09      (![X8 : $i]:
% 0.89/1.09         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.89/1.09          | ~ (v1_funct_1 @ X8)
% 0.89/1.09          | ~ (v1_relat_1 @ X8))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.09  thf('91', plain,
% 0.89/1.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ X3)
% 0.89/1.09          | ((k9_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.89/1.09              = (k9_relat_1 @ X3 @ (k9_relat_1 @ X4 @ X5)))
% 0.89/1.09          | ~ (v1_relat_1 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.89/1.09  thf('92', plain,
% 0.89/1.09      (![X17 : $i, X18 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X17)
% 0.89/1.09          | ((k10_relat_1 @ X17 @ X18)
% 0.89/1.09              = (k9_relat_1 @ (k2_funct_1 @ X17) @ X18))
% 0.89/1.09          | ~ (v1_funct_1 @ X17)
% 0.89/1.09          | ~ (v1_relat_1 @ X17))),
% 0.89/1.09      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.89/1.09  thf('93', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k10_relat_1 @ X1 @ (k9_relat_1 @ X2 @ X0))
% 0.89/1.09            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k2_funct_1 @ X1)) @ X0))
% 0.89/1.09          | ~ (v1_relat_1 @ X2)
% 0.89/1.09          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ~ (v1_funct_1 @ X1)
% 0.89/1.09          | ~ (v2_funct_1 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['91', '92'])).
% 0.89/1.09  thf('94', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v2_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X1 @ X2))
% 0.89/1.09              = (k9_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)) @ X2)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['90', '93'])).
% 0.89/1.09  thf('95', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X1 @ X2))
% 0.89/1.09            = (k9_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)) @ X2))
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ~ (v2_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_funct_1 @ X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['94'])).
% 0.89/1.09  thf('96', plain,
% 0.89/1.09      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.89/1.09        | ~ (v1_relat_1 @ sk_B)
% 0.89/1.09        | ~ (v1_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v2_funct_1 @ sk_B)
% 0.89/1.09        | ~ (v1_relat_1 @ sk_B))),
% 0.89/1.09      inference('sup+', [status(thm)], ['89', '95'])).
% 0.89/1.09  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('98', plain, ((v1_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('99', plain, ((v2_funct_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('100', plain, ((v1_relat_1 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('101', plain,
% 0.89/1.09      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.89/1.09  thf('102', plain,
% 0.89/1.09      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('103', plain, ($false),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.89/1.09  
% 0.89/1.09  % SZS output end Refutation
% 0.89/1.09  
% 0.89/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
