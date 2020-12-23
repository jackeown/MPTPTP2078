%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4MXKwZ9xbV

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 141 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  744 (1311 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ ( k9_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('11',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ ( k9_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('24',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
        = ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
        = ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','32'])).

thf('34',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('47',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','34','35','49','50'])).

thf('52',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','51'])).

thf('53',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4MXKwZ9xbV
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:54:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 62 iterations in 0.043s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(t94_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.19/0.49          | ~ (v1_relat_1 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.49  thf(t181_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( v1_relat_1 @ C ) =>
% 0.19/0.49           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.19/0.49             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X5)
% 0.19/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.19/0.49              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 0.19/0.49          | ~ (v1_relat_1 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.49  thf(t146_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.49         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.19/0.49          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ (k9_relat_1 @ X20 @ X19)))
% 0.19/0.49          | ~ (v1_relat_1 @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.19/0.49             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf(t97_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.49         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.19/0.49          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.19/0.49          | ~ (v1_relat_1 @ X12))),
% 0.19/0.49      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ((k7_relat_1 @ X0 @ 
% 0.19/0.49              (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.19/0.49              = (X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k7_relat_1 @ X0 @ 
% 0.19/0.49            (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))) = (
% 0.19/0.49            X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.19/0.49          | ~ (v1_relat_1 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.49  thf(t152_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.49       ( ( v2_funct_1 @ B ) =>
% 0.19/0.49         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (v2_funct_1 @ X21)
% 0.19/0.49          | (r1_tarski @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X22)) @ X22)
% 0.19/0.49          | ~ (v1_funct_1 @ X21)
% 0.19/0.49          | ~ (v1_relat_1 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.19/0.49  thf(t175_funct_2, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.49       ( ![B:$i,C:$i]:
% 0.19/0.49         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.49           ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.49             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.49          ( ![B:$i,C:$i]:
% 0.19/0.49            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.19/0.49              ( ( k10_relat_1 @ A @ C ) =
% 0.19/0.49                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.19/0.49  thf('11', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t71_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.49  thf('12', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.19/0.49          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ (k9_relat_1 @ X20 @ X19)))
% 0.19/0.49          | ~ (v1_relat_1 @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.49          | (r1_tarski @ X1 @ 
% 0.19/0.49             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.49              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf(fc3_funct_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('15', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.19/0.49          | (r1_tarski @ X1 @ 
% 0.19/0.49             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.49              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.19/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.19/0.49        (k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49         (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i, X2 : $i]:
% 0.19/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((~ (r1_tarski @ 
% 0.19/0.49           (k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))) @ 
% 0.19/0.49           (k10_relat_1 @ sk_A @ sk_C))
% 0.19/0.49        | ((k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.49        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.49        | ~ (v2_funct_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.49        | ((k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '19'])).
% 0.19/0.49  thf('21', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('22', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf(fc4_funct_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('23', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (((k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49         (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X5)
% 0.19/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.19/0.49              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 0.19/0.49          | ~ (v1_relat_1 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k10_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_B)) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49            = (k10_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k10_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_B)) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49            = (k10_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['9', '28'])).
% 0.19/0.49  thf('30', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('31', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 0.19/0.49           (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49           = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((((k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49          (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49          = (k10_relat_1 @ 
% 0.19/0.49             (k6_relat_1 @ 
% 0.19/0.49              (k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49               (k9_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49                (k1_relat_1 @ (k6_relat_1 @ sk_B))))) @ 
% 0.19/0.49             (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['8', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((k10_relat_1 @ (k6_relat_1 @ sk_B) @ 
% 0.19/0.49         (k9_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.19/0.49  thf('35', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.49  thf('36', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.19/0.49             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ X0 @ 
% 0.19/0.49           (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.49            (k9_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.49  thf('40', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r1_tarski @ X0 @ 
% 0.19/0.49          (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.49           (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (v2_funct_1 @ X21)
% 0.19/0.49          | (r1_tarski @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X22)) @ X22)
% 0.19/0.49          | ~ (v1_funct_1 @ X21)
% 0.19/0.49          | ~ (v1_relat_1 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X0 : $i, X2 : $i]:
% 0.19/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X1)
% 0.19/0.49          | ~ (v1_funct_1 @ X1)
% 0.19/0.49          | ~ (v2_funct_1 @ X1)
% 0.19/0.49          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.19/0.49          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((X0)
% 0.19/0.49            = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.49               (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 0.19/0.49          | ~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['41', '44'])).
% 0.19/0.49  thf('46', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.19/0.49  thf('47', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('48', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((X0)
% 0.19/0.49           = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.19/0.49              (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.19/0.49      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.19/0.49  thf('50', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.49         = (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['33', '34', '35', '49', '50'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.49          = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))
% 0.19/0.49        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['1', '51'])).
% 0.19/0.49  thf('53', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.49         = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.49          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '55'])).
% 0.19/0.49  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.49         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_A @ sk_C)
% 0.19/0.49         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('60', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
