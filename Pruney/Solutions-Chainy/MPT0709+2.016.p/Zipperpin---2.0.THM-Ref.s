%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2tZTHjMNaI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:07 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 597 expanded)
%              Number of leaves         :   30 ( 225 expanded)
%              Depth                    :   33
%              Number of atoms          : 2002 (5270 expanded)
%              Number of equality atoms :  103 ( 320 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
        = ( k6_relat_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
        = ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X10 ) )
      = ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k9_relat_1 @ X25 @ X26 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X25 ) @ X26 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','27'])).

thf('29',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('39',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('64',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','65'])).

thf('67',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X3 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['47','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X3 ) @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','72'])).

thf('74',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k9_relat_1 @ X25 @ X26 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X25 ) @ X26 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('80',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) @ X2 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('84',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('85',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('86',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf('90',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('91',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','62','63','64'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('93',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('105',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k10_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','62','63','64'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['89','121'])).

thf('123',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('124',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['122','123','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

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

thf('141',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) )).

thf('143',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k10_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) @ ( k9_relat_1 @ X27 @ X29 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t160_funct_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k9_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['140','149'])).

thf('151',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['138','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( r1_tarski @ ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('160',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['158','161'])).

thf('163',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['166','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2tZTHjMNaI
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:02:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.96/2.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.96/2.14  % Solved by: fo/fo7.sh
% 1.96/2.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.14  % done 969 iterations in 1.677s
% 1.96/2.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.96/2.14  % SZS output start Refutation
% 1.96/2.14  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.96/2.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.96/2.14  thf(sk_B_type, type, sk_B: $i).
% 1.96/2.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.96/2.14  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.96/2.14  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.96/2.14  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.96/2.14  thf(sk_A_type, type, sk_A: $i).
% 1.96/2.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.96/2.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.96/2.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.96/2.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.96/2.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.96/2.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.96/2.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.96/2.14  thf(t152_funct_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.96/2.14       ( ( v2_funct_1 @ B ) =>
% 1.96/2.14         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 1.96/2.14  thf('0', plain,
% 1.96/2.14      (![X23 : $i, X24 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X23)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X24)) @ X24)
% 1.96/2.14          | ~ (v1_funct_1 @ X23)
% 1.96/2.14          | ~ (v1_relat_1 @ X23))),
% 1.96/2.14      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.96/2.14  thf(t71_relat_1, axiom,
% 1.96/2.14    (![A:$i]:
% 1.96/2.14     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.96/2.14       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.96/2.14  thf('1', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.96/2.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.14  thf(t77_relat_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( v1_relat_1 @ B ) =>
% 1.96/2.14       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.96/2.14         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.96/2.14  thf('2', plain,
% 1.96/2.14      (![X11 : $i, X12 : $i]:
% 1.96/2.14         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.96/2.14          | ((k5_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 1.96/2.14          | ~ (v1_relat_1 @ X11))),
% 1.96/2.14      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.96/2.14  thf('3', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (r1_tarski @ X0 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.96/2.14              = (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup-', [status(thm)], ['1', '2'])).
% 1.96/2.14  thf(fc3_funct_1, axiom,
% 1.96/2.14    (![A:$i]:
% 1.96/2.14     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.96/2.14       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.96/2.14  thf('4', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('5', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (r1_tarski @ X0 @ X1)
% 1.96/2.14          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 1.96/2.14              = (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('demod', [status(thm)], ['3', '4'])).
% 1.96/2.14  thf('6', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_funct_1 @ X1)
% 1.96/2.14          | ~ (v2_funct_1 @ X1)
% 1.96/2.14          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.96/2.14              (k6_relat_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))
% 1.96/2.14              = (k6_relat_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['0', '5'])).
% 1.96/2.14  thf(t78_relat_1, axiom,
% 1.96/2.14    (![A:$i]:
% 1.96/2.14     ( ( v1_relat_1 @ A ) =>
% 1.96/2.14       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.96/2.14  thf('7', plain,
% 1.96/2.14      (![X13 : $i]:
% 1.96/2.14         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 1.96/2.14          | ~ (v1_relat_1 @ X13))),
% 1.96/2.14      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.96/2.14  thf(t94_relat_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( v1_relat_1 @ B ) =>
% 1.96/2.14       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.96/2.14  thf('8', plain,
% 1.96/2.14      (![X16 : $i, X17 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 1.96/2.14          | ~ (v1_relat_1 @ X17))),
% 1.96/2.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.96/2.14  thf('9', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X0)
% 1.96/2.14          | ~ (v1_relat_1 @ X0))),
% 1.96/2.14      inference('sup+', [status(thm)], ['7', '8'])).
% 1.96/2.14  thf('10', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 1.96/2.14      inference('simplify', [status(thm)], ['9'])).
% 1.96/2.14  thf(t148_relat_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( v1_relat_1 @ B ) =>
% 1.96/2.14       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.96/2.14  thf('11', plain,
% 1.96/2.14      (![X3 : $i, X4 : $i]:
% 1.96/2.14         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 1.96/2.14          | ~ (v1_relat_1 @ X3))),
% 1.96/2.14      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.96/2.14  thf('12', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf(d9_funct_1, axiom,
% 1.96/2.14    (![A:$i]:
% 1.96/2.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.96/2.14       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.96/2.14  thf('13', plain,
% 1.96/2.14      (![X18 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X18)
% 1.96/2.14          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 1.96/2.14          | ~ (v1_funct_1 @ X18)
% 1.96/2.14          | ~ (v1_relat_1 @ X18))),
% 1.96/2.14      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.96/2.14  thf('14', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ((k2_funct_1 @ (k6_relat_1 @ X0))
% 1.96/2.14              = (k4_relat_1 @ (k6_relat_1 @ X0)))
% 1.96/2.14          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup-', [status(thm)], ['12', '13'])).
% 1.96/2.14  thf('15', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf(t72_relat_1, axiom,
% 1.96/2.14    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.96/2.14  thf('16', plain,
% 1.96/2.14      (![X10 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X10)) = (k6_relat_1 @ X10))),
% 1.96/2.14      inference('cnf', [status(esa)], [t72_relat_1])).
% 1.96/2.14  thf(fc4_funct_1, axiom,
% 1.96/2.14    (![A:$i]:
% 1.96/2.14     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.96/2.14       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.96/2.14  thf('17', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.96/2.14  thf('18', plain,
% 1.96/2.14      (![X0 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.96/2.14  thf(t154_funct_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.96/2.14       ( ( v2_funct_1 @ B ) =>
% 1.96/2.14         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.96/2.14  thf('19', plain,
% 1.96/2.14      (![X25 : $i, X26 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X25)
% 1.96/2.14          | ((k9_relat_1 @ X25 @ X26)
% 1.96/2.14              = (k10_relat_1 @ (k2_funct_1 @ X25) @ X26))
% 1.96/2.14          | ~ (v1_funct_1 @ X25)
% 1.96/2.14          | ~ (v1_relat_1 @ X25))),
% 1.96/2.14      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.96/2.14  thf('20', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['18', '19'])).
% 1.96/2.14  thf('21', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('22', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('23', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.96/2.14  thf('24', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.96/2.14           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 1.96/2.14  thf('25', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['11', '24'])).
% 1.96/2.14  thf('26', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('27', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.96/2.14           = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['25', '26'])).
% 1.96/2.14  thf('28', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.96/2.14               (k1_relat_1 @ (k6_relat_1 @ X0))))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['10', '27'])).
% 1.96/2.14  thf('29', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 1.96/2.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.14  thf('30', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.96/2.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.14  thf('31', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('32', plain,
% 1.96/2.14      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.96/2.14  thf(t181_relat_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( v1_relat_1 @ B ) =>
% 1.96/2.14       ( ![C:$i]:
% 1.96/2.14         ( ( v1_relat_1 @ C ) =>
% 1.96/2.14           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.96/2.14             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 1.96/2.14  thf('33', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('34', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 1.96/2.14            = (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['32', '33'])).
% 1.96/2.14  thf('35', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('36', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 1.96/2.14            = (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['34', '35'])).
% 1.96/2.14  thf('37', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ 
% 1.96/2.14            (k6_relat_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))) @ 
% 1.96/2.14            (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.96/2.14               (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))
% 1.96/2.14          | ~ (v2_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['6', '36'])).
% 1.96/2.14  thf('38', plain,
% 1.96/2.14      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.96/2.14  thf('39', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('40', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.96/2.14               (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))
% 1.96/2.14          | ~ (v2_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.96/2.14  thf('41', plain,
% 1.96/2.14      (![X16 : $i, X17 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 1.96/2.14          | ~ (v1_relat_1 @ X17))),
% 1.96/2.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.96/2.14  thf('42', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('43', plain,
% 1.96/2.14      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.96/2.14  thf('44', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X1 @ X0)
% 1.96/2.14            = (k10_relat_1 @ 
% 1.96/2.14               (k5_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X1 @ X0)) @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X1 @ X0)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['42', '43'])).
% 1.96/2.14  thf('45', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('46', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X1 @ X0)
% 1.96/2.14            = (k10_relat_1 @ 
% 1.96/2.14               (k5_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ X1 @ X0)) @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['44', '45'])).
% 1.96/2.14  thf('47', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('48', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('49', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('50', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.96/2.14           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 1.96/2.14  thf('51', plain,
% 1.96/2.14      (![X23 : $i, X24 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X23)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X24)) @ X24)
% 1.96/2.14          | ~ (v1_funct_1 @ X23)
% 1.96/2.14          | ~ (v1_relat_1 @ X23))),
% 1.96/2.14      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.96/2.14  thf('52', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.96/2.14            (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.96/2.14           X0)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.96/2.14          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 1.96/2.14          | ~ (v2_funct_1 @ (k6_relat_1 @ X1)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['50', '51'])).
% 1.96/2.14  thf('53', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('54', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('55', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.96/2.14  thf('56', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (r1_tarski @ 
% 1.96/2.14          (k10_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.96/2.14          X0)),
% 1.96/2.14      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.96/2.14  thf('57', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ 
% 1.96/2.14            (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X1)) @ X0) @ 
% 1.96/2.14           X0)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['49', '56'])).
% 1.96/2.14  thf('58', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.96/2.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.14  thf('59', plain,
% 1.96/2.14      (![X13 : $i]:
% 1.96/2.14         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 1.96/2.14          | ~ (v1_relat_1 @ X13))),
% 1.96/2.14      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.96/2.14  thf('60', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.96/2.14            = (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['58', '59'])).
% 1.96/2.14  thf('61', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('62', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.96/2.14           = (k6_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['60', '61'])).
% 1.96/2.14  thf('63', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('64', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('65', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 1.96/2.14      inference('demod', [status(thm)], ['57', '62', '63', '64'])).
% 1.96/2.14  thf('66', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 1.96/2.14           (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['48', '65'])).
% 1.96/2.14  thf('67', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('68', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 1.96/2.14           (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['66', '67'])).
% 1.96/2.14  thf('69', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X3) @ X2) @ 
% 1.96/2.14            (k10_relat_1 @ X1 @ X0)) @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X2)
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X2))),
% 1.96/2.14      inference('sup+', [status(thm)], ['47', '68'])).
% 1.96/2.14  thf('70', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X2)
% 1.96/2.14          | (r1_tarski @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X3) @ X2) @ 
% 1.96/2.14              (k10_relat_1 @ X1 @ X0)) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)))),
% 1.96/2.14      inference('simplify', [status(thm)], ['69'])).
% 1.96/2.14  thf('71', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X2)
% 1.96/2.14          | ~ (v1_relat_1 @ X2)
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['46', '70'])).
% 1.96/2.14  thf('72', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X2)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)))),
% 1.96/2.14      inference('simplify', [status(thm)], ['71'])).
% 1.96/2.14  thf('73', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2)) @ 
% 1.96/2.14           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['41', '72'])).
% 1.96/2.14  thf('74', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('75', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2)) @ 
% 1.96/2.14           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['73', '74'])).
% 1.96/2.14  thf('76', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | (r1_tarski @ 
% 1.96/2.14             (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2)) @ 
% 1.96/2.14             (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 1.96/2.14      inference('simplify', [status(thm)], ['75'])).
% 1.96/2.14  thf('77', plain,
% 1.96/2.14      (![X16 : $i, X17 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 1.96/2.14          | ~ (v1_relat_1 @ X17))),
% 1.96/2.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.96/2.14  thf('78', plain,
% 1.96/2.14      (![X0 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.96/2.14  thf('79', plain,
% 1.96/2.14      (![X25 : $i, X26 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X25)
% 1.96/2.14          | ((k9_relat_1 @ X25 @ X26)
% 1.96/2.14              = (k10_relat_1 @ (k2_funct_1 @ X25) @ X26))
% 1.96/2.14          | ~ (v1_funct_1 @ X25)
% 1.96/2.14          | ~ (v1_relat_1 @ X25))),
% 1.96/2.14      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.96/2.14  thf('80', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('81', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (((k10_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X2) @ X1) @ X0)
% 1.96/2.14            = (k9_relat_1 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 1.96/2.14          | ~ (v1_relat_1 @ X2)
% 1.96/2.14          | ~ (v1_funct_1 @ X2)
% 1.96/2.14          | ~ (v2_funct_1 @ X2)
% 1.96/2.14          | ~ (v1_relat_1 @ (k2_funct_1 @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['79', '80'])).
% 1.96/2.14  thf('82', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | ((k10_relat_1 @ 
% 1.96/2.14              (k5_relat_1 @ (k2_funct_1 @ (k6_relat_1 @ X0)) @ X1) @ X2)
% 1.96/2.14              = (k9_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['78', '81'])).
% 1.96/2.14  thf('83', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('84', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.96/2.14  thf('85', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('86', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('87', plain,
% 1.96/2.14      (![X0 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.96/2.14  thf('88', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.96/2.14           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 1.96/2.14  thf('89', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2))))),
% 1.96/2.14      inference('demod', [status(thm)],
% 1.96/2.14                ['82', '83', '84', '85', '86', '87', '88'])).
% 1.96/2.14  thf('90', plain,
% 1.96/2.14      (![X13 : $i]:
% 1.96/2.14         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 1.96/2.14          | ~ (v1_relat_1 @ X13))),
% 1.96/2.14      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.96/2.14  thf('91', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('92', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 1.96/2.14      inference('demod', [status(thm)], ['57', '62', '63', '64'])).
% 1.96/2.14  thf(d10_xboole_0, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.96/2.14  thf('93', plain,
% 1.96/2.14      (![X0 : $i, X2 : $i]:
% 1.96/2.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.96/2.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.14  thf('94', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.96/2.14          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 1.96/2.14      inference('sup-', [status(thm)], ['92', '93'])).
% 1.96/2.14  thf('95', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ((k10_relat_1 @ X1 @ X0)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ X2) @ (k10_relat_1 @ X1 @ X0))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['91', '94'])).
% 1.96/2.14  thf('96', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('97', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ((k10_relat_1 @ X1 @ X0)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ X2) @ (k10_relat_1 @ X1 @ X0))))),
% 1.96/2.14      inference('demod', [status(thm)], ['95', '96'])).
% 1.96/2.14  thf('98', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k10_relat_1 @ X0 @ X1))
% 1.96/2.14          | ~ (v1_relat_1 @ X0)
% 1.96/2.14          | ((k10_relat_1 @ X0 @ X1)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14                 (k10_relat_1 @ X0 @ X1)))
% 1.96/2.14          | ~ (v1_relat_1 @ X0))),
% 1.96/2.14      inference('sup-', [status(thm)], ['90', '97'])).
% 1.96/2.14  thf('99', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.96/2.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.14  thf('100', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.96/2.14      inference('simplify', [status(thm)], ['99'])).
% 1.96/2.14  thf('101', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X0)
% 1.96/2.14          | ((k10_relat_1 @ X0 @ X1)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14                 (k10_relat_1 @ X0 @ X1)))
% 1.96/2.14          | ~ (v1_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['98', '100'])).
% 1.96/2.14  thf('102', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X0 @ X1)
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14               (k10_relat_1 @ X0 @ X1)))
% 1.96/2.14          | ~ (v1_relat_1 @ X0))),
% 1.96/2.14      inference('simplify', [status(thm)], ['101'])).
% 1.96/2.14  thf('103', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 1.96/2.14      inference('simplify', [status(thm)], ['9'])).
% 1.96/2.14  thf('104', plain,
% 1.96/2.14      (![X16 : $i, X17 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 1.96/2.14          | ~ (v1_relat_1 @ X17))),
% 1.96/2.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.96/2.14  thf('105', plain,
% 1.96/2.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X5)
% 1.96/2.14          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 1.96/2.14              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 1.96/2.14          | ~ (v1_relat_1 @ X6))),
% 1.96/2.14      inference('cnf', [status(esa)], [t181_relat_1])).
% 1.96/2.14  thf('106', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (r1_tarski @ 
% 1.96/2.14          (k10_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ 
% 1.96/2.14          X0)),
% 1.96/2.14      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.96/2.14  thf('107', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.96/2.14            (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)) @ 
% 1.96/2.14           (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['105', '106'])).
% 1.96/2.14  thf('108', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('109', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.96/2.14            (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)) @ 
% 1.96/2.14           (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['107', '108'])).
% 1.96/2.14  thf('110', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.96/2.14            (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 1.96/2.14           (k10_relat_1 @ X1 @ X2))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['104', '109'])).
% 1.96/2.14  thf('111', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | (r1_tarski @ 
% 1.96/2.14             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.96/2.14              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 1.96/2.14             (k10_relat_1 @ X1 @ X2)))),
% 1.96/2.14      inference('simplify', [status(thm)], ['110'])).
% 1.96/2.14  thf('112', plain,
% 1.96/2.14      (![X0 : $i, X2 : $i]:
% 1.96/2.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.96/2.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.14  thf('113', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.96/2.14               (k10_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.96/2.14                (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))
% 1.96/2.14          | ((k10_relat_1 @ X1 @ X0)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ X2) @ 
% 1.96/2.14                 (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['111', '112'])).
% 1.96/2.14  thf('114', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 1.96/2.14             (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14              (k10_relat_1 @ X0 @ X1)))
% 1.96/2.14          | ~ (v1_relat_1 @ X0)
% 1.96/2.14          | ((k10_relat_1 @ X0 @ X1)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14                 (k10_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1)))
% 1.96/2.14          | ~ (v1_relat_1 @ X0))),
% 1.96/2.14      inference('sup-', [status(thm)], ['103', '113'])).
% 1.96/2.14  thf('115', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X0 @ X1)
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14               (k10_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1)))
% 1.96/2.14          | ~ (v1_relat_1 @ X0)
% 1.96/2.14          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 1.96/2.14               (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.96/2.14                (k10_relat_1 @ X0 @ X1))))),
% 1.96/2.14      inference('simplify', [status(thm)], ['114'])).
% 1.96/2.14  thf('116', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (r1_tarski @ (k10_relat_1 @ X1 @ X0) @ (k10_relat_1 @ X1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ((k10_relat_1 @ X1 @ X0)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ 
% 1.96/2.14                 (k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1)) @ X0))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['102', '115'])).
% 1.96/2.14  thf('117', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.96/2.14      inference('simplify', [status(thm)], ['99'])).
% 1.96/2.14  thf('118', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ((k10_relat_1 @ X1 @ X0)
% 1.96/2.14              = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ 
% 1.96/2.14                 (k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1)) @ X0))))),
% 1.96/2.14      inference('demod', [status(thm)], ['116', '117'])).
% 1.96/2.14  thf('119', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X1 @ X0)
% 1.96/2.14            = (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ 
% 1.96/2.14               (k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1)) @ X0)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('simplify', [status(thm)], ['118'])).
% 1.96/2.14  thf('120', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 1.96/2.14      inference('demod', [status(thm)], ['57', '62', '63', '64'])).
% 1.96/2.14  thf('121', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 1.96/2.14           (k10_relat_1 @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X1)) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['119', '120'])).
% 1.96/2.14  thf('122', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 1.96/2.14           (k10_relat_1 @ 
% 1.96/2.14            (k7_relat_1 @ (k6_relat_1 @ X2) @ (k1_relat_1 @ (k6_relat_1 @ X2))) @ 
% 1.96/2.14            (k10_relat_1 @ X1 @ X0)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['89', '121'])).
% 1.96/2.14  thf('123', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.96/2.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.14  thf('124', plain,
% 1.96/2.14      (![X16 : $i, X17 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 1.96/2.14          | ~ (v1_relat_1 @ X17))),
% 1.96/2.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.96/2.14  thf('125', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 1.96/2.14           = (k6_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['60', '61'])).
% 1.96/2.14  thf('126', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['124', '125'])).
% 1.96/2.14  thf('127', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('128', plain,
% 1.96/2.14      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['126', '127'])).
% 1.96/2.14  thf('129', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('130', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ 
% 1.96/2.14           (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0) @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['122', '123', '128', '129'])).
% 1.96/2.14  thf('131', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 1.96/2.14           (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['77', '130'])).
% 1.96/2.14  thf('132', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 1.96/2.14             (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ X1 @ X2))))),
% 1.96/2.14      inference('simplify', [status(thm)], ['131'])).
% 1.96/2.14  thf('133', plain,
% 1.96/2.14      (![X0 : $i, X2 : $i]:
% 1.96/2.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.96/2.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.14  thf('134', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (r1_tarski @ 
% 1.96/2.14               (k10_relat_1 @ (k6_relat_1 @ X2) @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.96/2.14               (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 1.96/2.14          | ((k10_relat_1 @ (k6_relat_1 @ X2) @ (k10_relat_1 @ X1 @ X0))
% 1.96/2.14              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 1.96/2.14      inference('sup-', [status(thm)], ['132', '133'])).
% 1.96/2.14  thf('135', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X2)
% 1.96/2.14          | ((k10_relat_1 @ (k6_relat_1 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 1.96/2.14              = (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X2))),
% 1.96/2.14      inference('sup-', [status(thm)], ['76', '134'])).
% 1.96/2.14  thf('136', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (((k10_relat_1 @ (k6_relat_1 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 1.96/2.14            = (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.96/2.14          | ~ (v1_relat_1 @ X2))),
% 1.96/2.14      inference('simplify', [status(thm)], ['135'])).
% 1.96/2.14  thf('137', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (((k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))
% 1.96/2.14            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_funct_1 @ X1)
% 1.96/2.14          | ~ (v2_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup+', [status(thm)], ['40', '136'])).
% 1.96/2.14  thf('138', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_funct_1 @ X1)
% 1.96/2.14          | ~ (v1_relat_1 @ X1)
% 1.96/2.14          | ((k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))
% 1.96/2.14              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 1.96/2.14      inference('simplify', [status(thm)], ['137'])).
% 1.96/2.14  thf('139', plain,
% 1.96/2.14      (![X16 : $i, X17 : $i]:
% 1.96/2.14         (((k7_relat_1 @ X17 @ X16) = (k5_relat_1 @ (k6_relat_1 @ X16) @ X17))
% 1.96/2.14          | ~ (v1_relat_1 @ X17))),
% 1.96/2.14      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.96/2.14  thf('140', plain,
% 1.96/2.14      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 1.96/2.14      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.96/2.14  thf(t164_funct_1, conjecture,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.96/2.14       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.96/2.14         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.96/2.14  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.14    (~( ![A:$i,B:$i]:
% 1.96/2.14        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.96/2.14          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.96/2.14            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.96/2.14    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 1.96/2.14  thf('141', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('142', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 1.96/2.14      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.96/2.14  thf(t160_funct_1, axiom,
% 1.96/2.14    (![A:$i,B:$i]:
% 1.96/2.14     ( ( v1_relat_1 @ B ) =>
% 1.96/2.14       ( ![C:$i]:
% 1.96/2.14         ( ( v1_relat_1 @ C ) =>
% 1.96/2.14           ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ C ) ) =>
% 1.96/2.14             ( r1_tarski @
% 1.96/2.14               ( k10_relat_1 @ B @ A ) @ 
% 1.96/2.14               ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ) ))).
% 1.96/2.14  thf('143', plain,
% 1.96/2.14      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X27)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ X28 @ X29) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ X28 @ X27) @ (k9_relat_1 @ X27 @ X29)))
% 1.96/2.14          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X27))
% 1.96/2.14          | ~ (v1_relat_1 @ X28))),
% 1.96/2.14      inference('cnf', [status(esa)], [t160_funct_1])).
% 1.96/2.14  thf('144', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.96/2.14          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.96/2.14              (k9_relat_1 @ X1 @ X2)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('sup-', [status(thm)], ['142', '143'])).
% 1.96/2.14  thf('145', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 1.96/2.14      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.96/2.14  thf('146', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.14         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 1.96/2.14              (k9_relat_1 @ X1 @ X2)))
% 1.96/2.14          | ~ (v1_relat_1 @ X1))),
% 1.96/2.14      inference('demod', [status(thm)], ['144', '145'])).
% 1.96/2.14  thf('147', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ sk_B)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0) @ 
% 1.96/2.14             (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 1.96/2.14              (k9_relat_1 @ sk_B @ X0))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['141', '146'])).
% 1.96/2.14  thf('148', plain, ((v1_relat_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('149', plain,
% 1.96/2.14      (![X0 : $i]:
% 1.96/2.14         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ X0) @ 
% 1.96/2.14          (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 1.96/2.14           (k9_relat_1 @ sk_B @ X0)))),
% 1.96/2.14      inference('demod', [status(thm)], ['147', '148'])).
% 1.96/2.14  thf('150', plain,
% 1.96/2.14      ((r1_tarski @ sk_A @ 
% 1.96/2.14        (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 1.96/2.14         (k9_relat_1 @ sk_B @ sk_A)))),
% 1.96/2.14      inference('sup+', [status(thm)], ['140', '149'])).
% 1.96/2.14  thf('151', plain,
% 1.96/2.14      (((r1_tarski @ sk_A @ 
% 1.96/2.14         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.96/2.14        | ~ (v1_relat_1 @ sk_B))),
% 1.96/2.14      inference('sup+', [status(thm)], ['139', '150'])).
% 1.96/2.14  thf('152', plain, ((v1_relat_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('153', plain,
% 1.96/2.14      ((r1_tarski @ sk_A @ 
% 1.96/2.14        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.96/2.14      inference('demod', [status(thm)], ['151', '152'])).
% 1.96/2.14  thf('154', plain,
% 1.96/2.14      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.96/2.14        | ~ (v1_relat_1 @ sk_B)
% 1.96/2.14        | ~ (v1_funct_1 @ sk_B)
% 1.96/2.14        | ~ (v2_funct_1 @ sk_B))),
% 1.96/2.14      inference('sup+', [status(thm)], ['138', '153'])).
% 1.96/2.14  thf('155', plain, ((v1_relat_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('156', plain, ((v1_funct_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('157', plain, ((v2_funct_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('158', plain,
% 1.96/2.14      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.96/2.14      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 1.96/2.14  thf('159', plain,
% 1.96/2.14      (![X23 : $i, X24 : $i]:
% 1.96/2.14         (~ (v2_funct_1 @ X23)
% 1.96/2.14          | (r1_tarski @ (k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X24)) @ X24)
% 1.96/2.14          | ~ (v1_funct_1 @ X23)
% 1.96/2.14          | ~ (v1_relat_1 @ X23))),
% 1.96/2.14      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.96/2.14  thf('160', plain,
% 1.96/2.14      (![X0 : $i, X2 : $i]:
% 1.96/2.14         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.96/2.14      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.14  thf('161', plain,
% 1.96/2.14      (![X0 : $i, X1 : $i]:
% 1.96/2.14         (~ (v1_relat_1 @ X1)
% 1.96/2.14          | ~ (v1_funct_1 @ X1)
% 1.96/2.14          | ~ (v2_funct_1 @ X1)
% 1.96/2.14          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.96/2.14          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 1.96/2.14      inference('sup-', [status(thm)], ['159', '160'])).
% 1.96/2.14  thf('162', plain,
% 1.96/2.14      ((((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.96/2.14        | ~ (v2_funct_1 @ sk_B)
% 1.96/2.14        | ~ (v1_funct_1 @ sk_B)
% 1.96/2.14        | ~ (v1_relat_1 @ sk_B))),
% 1.96/2.14      inference('sup-', [status(thm)], ['158', '161'])).
% 1.96/2.14  thf('163', plain, ((v2_funct_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('164', plain, ((v1_funct_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('165', plain, ((v1_relat_1 @ sk_B)),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('166', plain,
% 1.96/2.14      (((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.96/2.14      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 1.96/2.14  thf('167', plain,
% 1.96/2.14      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.96/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.14  thf('168', plain, ($false),
% 1.96/2.14      inference('simplify_reflect-', [status(thm)], ['166', '167'])).
% 1.96/2.14  
% 1.96/2.14  % SZS output end Refutation
% 1.96/2.14  
% 1.96/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
