%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mjpi1OI2MG

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:17 EST 2020

% Result     : Theorem 9.25s
% Output     : Refutation 9.25s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 511 expanded)
%              Number of leaves         :   47 ( 184 expanded)
%              Depth                    :   28
%              Number of atoms          : 1325 (4064 expanded)
%              Number of equality atoms :  101 ( 308 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X57 @ X56 ) @ X58 )
        = ( k3_xboole_0 @ X56 @ ( k10_relat_1 @ X57 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('2',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X57 @ X56 ) @ X58 )
        = ( k3_xboole_0 @ X56 @ ( k10_relat_1 @ X57 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X37: $i] :
      ( ( ( k10_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X57 @ X56 ) @ X58 )
        = ( k3_xboole_0 @ X56 @ ( k10_relat_1 @ X57 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('9',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k7_relat_1 @ X50 @ X49 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X49 ) @ X50 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) )
        = ( k10_relat_1 @ X42 @ ( k1_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X11 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('29',plain,
    ( ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('30',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X37: $i] :
      ( ( ( k10_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k10_relat_1 @ X53 @ ( k6_subset_1 @ X54 @ X55 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X53 @ X54 ) @ ( k10_relat_1 @ X53 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k6_subset_1 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X52: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ k1_xboole_0 )
    = ( k6_subset_1 @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('44',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X45 ) @ X46 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X46 ) @ X45 )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ k1_xboole_0 ) )
      = ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X37: $i] :
      ( ( ( k10_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k10_relat_1 @ X39 @ ( k10_relat_1 @ X38 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('56',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X35 @ X36 ) @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('64',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54','61','62','63','64'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('68',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k2_xboole_0 @ X21 @ ( k6_subset_1 @ X22 @ X21 ) ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_subset_1 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( sk_A
    = ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k2_xboole_0 @ X21 @ ( k6_subset_1 @ X22 @ X21 ) ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('76',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k6_subset_1 @ X25 @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('78',plain,(
    ! [X13: $i] :
      ( ( k6_subset_1 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','81'])).

thf('83',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','82'])).

thf('84',plain,(
    ! [X51: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X35 @ X36 ) @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','99'])).

thf('101',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['100','101','103','104'])).

thf('106',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('109',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('110',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('118',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X34 @ X33 ) @ X32 )
        = ( k9_relat_1 @ X34 @ X32 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('122',plain,(
    ! [X31: $i] :
      ( ( ( k9_relat_1 @ X31 @ ( k1_relat_1 @ X31 ) )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('123',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['119','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['0','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mjpi1OI2MG
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 9.25/9.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.25/9.46  % Solved by: fo/fo7.sh
% 9.25/9.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.25/9.46  % done 11697 iterations in 8.974s
% 9.25/9.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.25/9.46  % SZS output start Refutation
% 9.25/9.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.25/9.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.25/9.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.25/9.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.25/9.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 9.25/9.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 9.25/9.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.25/9.46  thf(sk_B_type, type, sk_B: $i).
% 9.25/9.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.25/9.46  thf(sk_A_type, type, sk_A: $i).
% 9.25/9.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.25/9.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.25/9.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.25/9.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.25/9.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 9.25/9.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 9.25/9.46  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 9.25/9.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.25/9.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.25/9.46  thf(t146_funct_1, conjecture,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ B ) =>
% 9.25/9.46       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 9.25/9.46         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 9.25/9.46  thf(zf_stmt_0, negated_conjecture,
% 9.25/9.46    (~( ![A:$i,B:$i]:
% 9.25/9.46        ( ( v1_relat_1 @ B ) =>
% 9.25/9.46          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 9.25/9.46            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 9.25/9.46    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 9.25/9.46  thf('0', plain,
% 9.25/9.46      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf(t139_funct_1, axiom,
% 9.25/9.46    (![A:$i,B:$i,C:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ C ) =>
% 9.25/9.46       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 9.25/9.46         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 9.25/9.46  thf('1', plain,
% 9.25/9.46      (![X56 : $i, X57 : $i, X58 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k7_relat_1 @ X57 @ X56) @ X58)
% 9.25/9.46            = (k3_xboole_0 @ X56 @ (k10_relat_1 @ X57 @ X58)))
% 9.25/9.46          | ~ (v1_relat_1 @ X57))),
% 9.25/9.46      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.25/9.46  thf('2', plain,
% 9.25/9.46      (![X56 : $i, X57 : $i, X58 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k7_relat_1 @ X57 @ X56) @ X58)
% 9.25/9.46            = (k3_xboole_0 @ X56 @ (k10_relat_1 @ X57 @ X58)))
% 9.25/9.46          | ~ (v1_relat_1 @ X57))),
% 9.25/9.46      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.25/9.46  thf(t169_relat_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ A ) =>
% 9.25/9.46       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 9.25/9.46  thf('3', plain,
% 9.25/9.46      (![X37 : $i]:
% 9.25/9.46         (((k10_relat_1 @ X37 @ (k2_relat_1 @ X37)) = (k1_relat_1 @ X37))
% 9.25/9.46          | ~ (v1_relat_1 @ X37))),
% 9.25/9.46      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.25/9.46  thf('4', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (((k3_xboole_0 @ X0 @ 
% 9.25/9.46            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 9.25/9.46            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 9.25/9.46          | ~ (v1_relat_1 @ X1)
% 9.25/9.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['2', '3'])).
% 9.25/9.46  thf(dt_k7_relat_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 9.25/9.46  thf('5', plain,
% 9.25/9.46      (![X29 : $i, X30 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k7_relat_1 @ X29 @ X30)))),
% 9.25/9.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.25/9.46  thf('6', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X1)
% 9.25/9.46          | ((k3_xboole_0 @ X0 @ 
% 9.25/9.46              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 9.25/9.46              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 9.25/9.46      inference('clc', [status(thm)], ['4', '5'])).
% 9.25/9.46  thf('7', plain,
% 9.25/9.46      (![X56 : $i, X57 : $i, X58 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k7_relat_1 @ X57 @ X56) @ X58)
% 9.25/9.46            = (k3_xboole_0 @ X56 @ (k10_relat_1 @ X57 @ X58)))
% 9.25/9.46          | ~ (v1_relat_1 @ X57))),
% 9.25/9.46      inference('cnf', [status(esa)], [t139_funct_1])).
% 9.25/9.46  thf('8', plain,
% 9.25/9.46      (![X29 : $i, X30 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k7_relat_1 @ X29 @ X30)))),
% 9.25/9.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.25/9.46  thf(t94_relat_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ B ) =>
% 9.25/9.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 9.25/9.46  thf('9', plain,
% 9.25/9.46      (![X49 : $i, X50 : $i]:
% 9.25/9.46         (((k7_relat_1 @ X50 @ X49) = (k5_relat_1 @ (k6_relat_1 @ X49) @ X50))
% 9.25/9.46          | ~ (v1_relat_1 @ X50))),
% 9.25/9.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 9.25/9.46  thf(t182_relat_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ A ) =>
% 9.25/9.46       ( ![B:$i]:
% 9.25/9.46         ( ( v1_relat_1 @ B ) =>
% 9.25/9.46           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 9.25/9.46             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 9.25/9.46  thf('10', plain,
% 9.25/9.46      (![X41 : $i, X42 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X41)
% 9.25/9.46          | ((k1_relat_1 @ (k5_relat_1 @ X42 @ X41))
% 9.25/9.46              = (k10_relat_1 @ X42 @ (k1_relat_1 @ X41)))
% 9.25/9.46          | ~ (v1_relat_1 @ X42))),
% 9.25/9.46      inference('cnf', [status(esa)], [t182_relat_1])).
% 9.25/9.46  thf(commutativity_k2_xboole_0, axiom,
% 9.25/9.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 9.25/9.46  thf('11', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.25/9.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.25/9.46  thf(t36_xboole_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.25/9.46  thf('12', plain,
% 9.25/9.46      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 9.25/9.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.25/9.46  thf(redefinition_k6_subset_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.25/9.46  thf('13', plain,
% 9.25/9.46      (![X25 : $i, X26 : $i]:
% 9.25/9.46         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 9.25/9.46      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.25/9.46  thf('14', plain,
% 9.25/9.46      (![X11 : $i, X12 : $i]: (r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X11)),
% 9.25/9.46      inference('demod', [status(thm)], ['12', '13'])).
% 9.25/9.46  thf(t44_xboole_1, axiom,
% 9.25/9.46    (![A:$i,B:$i,C:$i]:
% 9.25/9.46     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 9.25/9.46       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.25/9.46  thf('15', plain,
% 9.25/9.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.25/9.46         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 9.25/9.46          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 9.25/9.46      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.25/9.46  thf('16', plain,
% 9.25/9.46      (![X25 : $i, X26 : $i]:
% 9.25/9.46         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 9.25/9.46      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.25/9.46  thf('17', plain,
% 9.25/9.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.25/9.46         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 9.25/9.46          | ~ (r1_tarski @ (k6_subset_1 @ X18 @ X19) @ X20))),
% 9.25/9.46      inference('demod', [status(thm)], ['15', '16'])).
% 9.25/9.46  thf('18', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.25/9.46      inference('sup-', [status(thm)], ['14', '17'])).
% 9.25/9.46  thf('19', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf(t1_xboole_1, axiom,
% 9.25/9.46    (![A:$i,B:$i,C:$i]:
% 9.25/9.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 9.25/9.46       ( r1_tarski @ A @ C ) ))).
% 9.25/9.46  thf('20', plain,
% 9.25/9.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 9.25/9.46         (~ (r1_tarski @ X7 @ X8)
% 9.25/9.46          | ~ (r1_tarski @ X8 @ X9)
% 9.25/9.46          | (r1_tarski @ X7 @ X9))),
% 9.25/9.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.25/9.46  thf('21', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 9.25/9.46      inference('sup-', [status(thm)], ['19', '20'])).
% 9.25/9.46  thf('22', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)))),
% 9.25/9.46      inference('sup-', [status(thm)], ['18', '21'])).
% 9.25/9.46  thf('23', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 9.25/9.46      inference('sup+', [status(thm)], ['11', '22'])).
% 9.25/9.46  thf(t43_xboole_1, axiom,
% 9.25/9.46    (![A:$i,B:$i,C:$i]:
% 9.25/9.46     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 9.25/9.46       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 9.25/9.46  thf('24', plain,
% 9.25/9.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.25/9.46         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 9.25/9.46          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 9.25/9.46      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.25/9.46  thf('25', plain,
% 9.25/9.46      (![X25 : $i, X26 : $i]:
% 9.25/9.46         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 9.25/9.46      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.25/9.46  thf('26', plain,
% 9.25/9.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.25/9.46         ((r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)
% 9.25/9.46          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 9.25/9.46      inference('demod', [status(thm)], ['24', '25'])).
% 9.25/9.46  thf('27', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (r1_tarski @ (k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)),
% 9.25/9.46      inference('sup-', [status(thm)], ['23', '26'])).
% 9.25/9.46  thf(t3_xboole_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.25/9.46  thf('28', plain,
% 9.25/9.46      (![X14 : $i]:
% 9.25/9.46         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 9.25/9.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 9.25/9.46  thf('29', plain,
% 9.25/9.46      (((k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 9.25/9.46      inference('sup-', [status(thm)], ['27', '28'])).
% 9.25/9.46  thf(t71_relat_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.25/9.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.25/9.46  thf('30', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 9.25/9.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.25/9.46  thf('31', plain,
% 9.25/9.46      (![X37 : $i]:
% 9.25/9.46         (((k10_relat_1 @ X37 @ (k2_relat_1 @ X37)) = (k1_relat_1 @ X37))
% 9.25/9.46          | ~ (v1_relat_1 @ X37))),
% 9.25/9.46      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.25/9.46  thf('32', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 9.25/9.46            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 9.25/9.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['30', '31'])).
% 9.25/9.46  thf('33', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 9.25/9.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.25/9.46  thf(fc3_funct_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.25/9.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.25/9.46  thf('34', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('35', plain,
% 9.25/9.46      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 9.25/9.46      inference('demod', [status(thm)], ['32', '33', '34'])).
% 9.25/9.46  thf(t138_funct_1, axiom,
% 9.25/9.46    (![A:$i,B:$i,C:$i]:
% 9.25/9.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 9.25/9.46       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 9.25/9.46         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 9.25/9.46  thf('36', plain,
% 9.25/9.46      (![X53 : $i, X54 : $i, X55 : $i]:
% 9.25/9.46         (((k10_relat_1 @ X53 @ (k6_subset_1 @ X54 @ X55))
% 9.25/9.46            = (k6_subset_1 @ (k10_relat_1 @ X53 @ X54) @ 
% 9.25/9.46               (k10_relat_1 @ X53 @ X55)))
% 9.25/9.46          | ~ (v1_funct_1 @ X53)
% 9.25/9.46          | ~ (v1_relat_1 @ X53))),
% 9.25/9.46      inference('cnf', [status(esa)], [t138_funct_1])).
% 9.25/9.46  thf('37', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k6_subset_1 @ X0 @ X1))
% 9.25/9.46            = (k6_subset_1 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 9.25/9.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.25/9.46          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['35', '36'])).
% 9.25/9.46  thf('38', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('39', plain, (![X52 : $i]: (v1_funct_1 @ (k6_relat_1 @ X52))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('40', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k6_subset_1 @ X0 @ X1))
% 9.25/9.46           = (k6_subset_1 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 9.25/9.46      inference('demod', [status(thm)], ['37', '38', '39'])).
% 9.25/9.46  thf('41', plain,
% 9.25/9.46      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ k1_xboole_0)
% 9.25/9.46         = (k6_subset_1 @ sk_A @ 
% 9.25/9.46            (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 9.25/9.46      inference('sup+', [status(thm)], ['29', '40'])).
% 9.25/9.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.25/9.46  thf('42', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 9.25/9.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.25/9.46  thf('43', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 9.25/9.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.25/9.46  thf(t77_relat_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ B ) =>
% 9.25/9.46       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 9.25/9.46         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 9.25/9.46  thf('44', plain,
% 9.25/9.46      (![X45 : $i, X46 : $i]:
% 9.25/9.46         (~ (r1_tarski @ (k1_relat_1 @ X45) @ X46)
% 9.25/9.46          | ((k5_relat_1 @ (k6_relat_1 @ X46) @ X45) = (X45))
% 9.25/9.46          | ~ (v1_relat_1 @ X45))),
% 9.25/9.46      inference('cnf', [status(esa)], [t77_relat_1])).
% 9.25/9.46  thf('45', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (~ (r1_tarski @ X0 @ X1)
% 9.25/9.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.25/9.46          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 9.25/9.46              = (k6_relat_1 @ X0)))),
% 9.25/9.46      inference('sup-', [status(thm)], ['43', '44'])).
% 9.25/9.46  thf('46', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('47', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (~ (r1_tarski @ X0 @ X1)
% 9.25/9.46          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 9.25/9.46              = (k6_relat_1 @ X0)))),
% 9.25/9.46      inference('demod', [status(thm)], ['45', '46'])).
% 9.25/9.46  thf('48', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ k1_xboole_0))
% 9.25/9.46           = (k6_relat_1 @ k1_xboole_0))),
% 9.25/9.46      inference('sup-', [status(thm)], ['42', '47'])).
% 9.25/9.46  thf('49', plain,
% 9.25/9.46      (![X37 : $i]:
% 9.25/9.46         (((k10_relat_1 @ X37 @ (k2_relat_1 @ X37)) = (k1_relat_1 @ X37))
% 9.25/9.46          | ~ (v1_relat_1 @ X37))),
% 9.25/9.46      inference('cnf', [status(esa)], [t169_relat_1])).
% 9.25/9.46  thf(t181_relat_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ B ) =>
% 9.25/9.46       ( ![C:$i]:
% 9.25/9.46         ( ( v1_relat_1 @ C ) =>
% 9.25/9.46           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 9.25/9.46             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 9.25/9.46  thf('50', plain,
% 9.25/9.46      (![X38 : $i, X39 : $i, X40 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X38)
% 9.25/9.46          | ((k10_relat_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 9.25/9.46              = (k10_relat_1 @ X39 @ (k10_relat_1 @ X38 @ X40)))
% 9.25/9.46          | ~ (v1_relat_1 @ X39))),
% 9.25/9.46      inference('cnf', [status(esa)], [t181_relat_1])).
% 9.25/9.46  thf('51', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 9.25/9.46            = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 9.25/9.46          | ~ (v1_relat_1 @ X0)
% 9.25/9.46          | ~ (v1_relat_1 @ X1)
% 9.25/9.46          | ~ (v1_relat_1 @ X0))),
% 9.25/9.46      inference('sup+', [status(thm)], ['49', '50'])).
% 9.25/9.46  thf('52', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X1)
% 9.25/9.46          | ~ (v1_relat_1 @ X0)
% 9.25/9.46          | ((k10_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 9.25/9.46              = (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 9.25/9.46      inference('simplify', [status(thm)], ['51'])).
% 9.25/9.46  thf('53', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (((k10_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ 
% 9.25/9.46            (k2_relat_1 @ (k6_relat_1 @ k1_xboole_0)))
% 9.25/9.46            = (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 9.25/9.46               (k1_relat_1 @ (k6_relat_1 @ k1_xboole_0))))
% 9.25/9.46          | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0))
% 9.25/9.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['48', '52'])).
% 9.25/9.46  thf('54', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 9.25/9.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.25/9.46  thf('55', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 9.25/9.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.25/9.46  thf(t167_relat_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ B ) =>
% 9.25/9.46       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 9.25/9.46  thf('56', plain,
% 9.25/9.46      (![X35 : $i, X36 : $i]:
% 9.25/9.46         ((r1_tarski @ (k10_relat_1 @ X35 @ X36) @ (k1_relat_1 @ X35))
% 9.25/9.46          | ~ (v1_relat_1 @ X35))),
% 9.25/9.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 9.25/9.46  thf('57', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 9.25/9.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['55', '56'])).
% 9.25/9.46  thf('58', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('59', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 9.25/9.46      inference('demod', [status(thm)], ['57', '58'])).
% 9.25/9.46  thf('60', plain,
% 9.25/9.46      (![X14 : $i]:
% 9.25/9.46         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 9.25/9.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 9.25/9.46  thf('61', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         ((k10_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 9.25/9.46      inference('sup-', [status(thm)], ['59', '60'])).
% 9.25/9.46  thf('62', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 9.25/9.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.25/9.46  thf('63', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('64', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('65', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         ((k1_xboole_0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0))),
% 9.25/9.46      inference('demod', [status(thm)], ['53', '54', '61', '62', '63', '64'])).
% 9.25/9.46  thf('66', plain,
% 9.25/9.46      (((k1_xboole_0)
% 9.25/9.46         = (k6_subset_1 @ sk_A @ 
% 9.25/9.46            (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 9.25/9.46      inference('demod', [status(thm)], ['41', '65'])).
% 9.25/9.46  thf('67', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 9.25/9.46      inference('demod', [status(thm)], ['57', '58'])).
% 9.25/9.46  thf(t45_xboole_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( r1_tarski @ A @ B ) =>
% 9.25/9.46       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 9.25/9.46  thf('68', plain,
% 9.25/9.46      (![X21 : $i, X22 : $i]:
% 9.25/9.46         (((X22) = (k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))
% 9.25/9.46          | ~ (r1_tarski @ X21 @ X22))),
% 9.25/9.46      inference('cnf', [status(esa)], [t45_xboole_1])).
% 9.25/9.46  thf('69', plain,
% 9.25/9.46      (![X25 : $i, X26 : $i]:
% 9.25/9.46         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 9.25/9.46      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.25/9.46  thf('70', plain,
% 9.25/9.46      (![X21 : $i, X22 : $i]:
% 9.25/9.46         (((X22) = (k2_xboole_0 @ X21 @ (k6_subset_1 @ X22 @ X21)))
% 9.25/9.46          | ~ (r1_tarski @ X21 @ X22))),
% 9.25/9.46      inference('demod', [status(thm)], ['68', '69'])).
% 9.25/9.46  thf('71', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         ((X0)
% 9.25/9.46           = (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 9.25/9.46              (k6_subset_1 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 9.25/9.46      inference('sup-', [status(thm)], ['67', '70'])).
% 9.25/9.46  thf('72', plain,
% 9.25/9.46      (((sk_A)
% 9.25/9.46         = (k2_xboole_0 @ 
% 9.25/9.46            (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 9.25/9.46            k1_xboole_0))),
% 9.25/9.46      inference('sup+', [status(thm)], ['66', '71'])).
% 9.25/9.46  thf('73', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 9.25/9.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.25/9.46  thf('74', plain,
% 9.25/9.46      (![X21 : $i, X22 : $i]:
% 9.25/9.46         (((X22) = (k2_xboole_0 @ X21 @ (k6_subset_1 @ X22 @ X21)))
% 9.25/9.46          | ~ (r1_tarski @ X21 @ X22))),
% 9.25/9.46      inference('demod', [status(thm)], ['68', '69'])).
% 9.25/9.46  thf('75', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k6_subset_1 @ X0 @ k1_xboole_0)))),
% 9.25/9.46      inference('sup-', [status(thm)], ['73', '74'])).
% 9.25/9.46  thf(t3_boole, axiom,
% 9.25/9.46    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.25/9.46  thf('76', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 9.25/9.46      inference('cnf', [status(esa)], [t3_boole])).
% 9.25/9.46  thf('77', plain,
% 9.25/9.46      (![X25 : $i, X26 : $i]:
% 9.25/9.46         ((k6_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))),
% 9.25/9.46      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.25/9.46  thf('78', plain, (![X13 : $i]: ((k6_subset_1 @ X13 @ k1_xboole_0) = (X13))),
% 9.25/9.46      inference('demod', [status(thm)], ['76', '77'])).
% 9.25/9.46  thf('79', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 9.25/9.46      inference('demod', [status(thm)], ['75', '78'])).
% 9.25/9.46  thf('80', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.25/9.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.25/9.46  thf('81', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.25/9.46      inference('sup+', [status(thm)], ['79', '80'])).
% 9.25/9.46  thf('82', plain,
% 9.25/9.46      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 9.25/9.46      inference('demod', [status(thm)], ['72', '81'])).
% 9.25/9.46  thf('83', plain,
% 9.25/9.46      ((((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 9.25/9.46        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 9.25/9.46        | ~ (v1_relat_1 @ sk_B))),
% 9.25/9.46      inference('sup+', [status(thm)], ['10', '82'])).
% 9.25/9.46  thf('84', plain, (![X51 : $i]: (v1_relat_1 @ (k6_relat_1 @ X51))),
% 9.25/9.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.25/9.46  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('86', plain,
% 9.25/9.46      (((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 9.25/9.46      inference('demod', [status(thm)], ['83', '84', '85'])).
% 9.25/9.46  thf('87', plain,
% 9.25/9.46      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 9.25/9.46        | ~ (v1_relat_1 @ sk_B))),
% 9.25/9.46      inference('sup+', [status(thm)], ['9', '86'])).
% 9.25/9.46  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('89', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('demod', [status(thm)], ['87', '88'])).
% 9.25/9.46  thf('90', plain,
% 9.25/9.46      (![X35 : $i, X36 : $i]:
% 9.25/9.46         ((r1_tarski @ (k10_relat_1 @ X35 @ X36) @ (k1_relat_1 @ X35))
% 9.25/9.46          | ~ (v1_relat_1 @ X35))),
% 9.25/9.46      inference('cnf', [status(esa)], [t167_relat_1])).
% 9.25/9.46  thf('91', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 9.25/9.46          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['89', '90'])).
% 9.25/9.46  thf('92', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ sk_B)
% 9.25/9.46          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 9.25/9.46      inference('sup-', [status(thm)], ['8', '91'])).
% 9.25/9.46  thf('93', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('94', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 9.25/9.46      inference('demod', [status(thm)], ['92', '93'])).
% 9.25/9.46  thf(d10_xboole_0, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.25/9.46  thf('95', plain,
% 9.25/9.46      (![X2 : $i, X4 : $i]:
% 9.25/9.46         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 9.25/9.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.25/9.46  thf('96', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 9.25/9.46          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 9.25/9.46      inference('sup-', [status(thm)], ['94', '95'])).
% 9.25/9.46  thf('97', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (~ (r1_tarski @ sk_A @ 
% 9.25/9.46             (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 9.25/9.46          | ~ (v1_relat_1 @ sk_B)
% 9.25/9.46          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 9.25/9.46      inference('sup-', [status(thm)], ['7', '96'])).
% 9.25/9.46  thf('98', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('99', plain,
% 9.25/9.46      (![X0 : $i]:
% 9.25/9.46         (~ (r1_tarski @ sk_A @ 
% 9.25/9.46             (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 9.25/9.46          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 9.25/9.46      inference('demod', [status(thm)], ['97', '98'])).
% 9.25/9.46  thf('100', plain,
% 9.25/9.46      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 9.25/9.46        | ~ (v1_relat_1 @ sk_B)
% 9.25/9.46        | ((sk_A)
% 9.25/9.46            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 9.25/9.46               (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 9.25/9.46      inference('sup-', [status(thm)], ['6', '99'])).
% 9.25/9.46  thf('101', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('demod', [status(thm)], ['87', '88'])).
% 9.25/9.46  thf('102', plain,
% 9.25/9.46      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 9.25/9.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.25/9.46  thf('103', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.25/9.46      inference('simplify', [status(thm)], ['102'])).
% 9.25/9.46  thf('104', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('105', plain,
% 9.25/9.46      (((sk_A)
% 9.25/9.46         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 9.25/9.46            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 9.25/9.46      inference('demod', [status(thm)], ['100', '101', '103', '104'])).
% 9.25/9.46  thf('106', plain,
% 9.25/9.46      ((((sk_A)
% 9.25/9.46          = (k3_xboole_0 @ sk_A @ 
% 9.25/9.46             (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))
% 9.25/9.46        | ~ (v1_relat_1 @ sk_B))),
% 9.25/9.46      inference('sup+', [status(thm)], ['1', '105'])).
% 9.25/9.46  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('108', plain,
% 9.25/9.46      (((sk_A)
% 9.25/9.46         = (k3_xboole_0 @ sk_A @ 
% 9.25/9.46            (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 9.25/9.46      inference('demod', [status(thm)], ['106', '107'])).
% 9.25/9.46  thf(commutativity_k2_tarski, axiom,
% 9.25/9.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 9.25/9.46  thf('109', plain,
% 9.25/9.46      (![X23 : $i, X24 : $i]:
% 9.25/9.46         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 9.25/9.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.25/9.46  thf(t12_setfam_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]:
% 9.25/9.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.25/9.46  thf('110', plain,
% 9.25/9.46      (![X27 : $i, X28 : $i]:
% 9.25/9.46         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 9.25/9.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.25/9.46  thf('111', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 9.25/9.46      inference('sup+', [status(thm)], ['109', '110'])).
% 9.25/9.46  thf('112', plain,
% 9.25/9.46      (![X27 : $i, X28 : $i]:
% 9.25/9.46         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 9.25/9.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.25/9.46  thf('113', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.25/9.46      inference('sup+', [status(thm)], ['111', '112'])).
% 9.25/9.46  thf(t17_xboole_1, axiom,
% 9.25/9.46    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 9.25/9.46  thf('114', plain,
% 9.25/9.46      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 9.25/9.46      inference('cnf', [status(esa)], [t17_xboole_1])).
% 9.25/9.46  thf('115', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 9.25/9.46      inference('sup+', [status(thm)], ['113', '114'])).
% 9.25/9.46  thf('116', plain,
% 9.25/9.46      ((r1_tarski @ sk_A @ 
% 9.25/9.46        (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 9.25/9.46      inference('sup+', [status(thm)], ['108', '115'])).
% 9.25/9.46  thf('117', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.25/9.46      inference('simplify', [status(thm)], ['102'])).
% 9.25/9.46  thf(t162_relat_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ A ) =>
% 9.25/9.46       ( ![B:$i,C:$i]:
% 9.25/9.46         ( ( r1_tarski @ B @ C ) =>
% 9.25/9.46           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 9.25/9.46             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 9.25/9.46  thf('118', plain,
% 9.25/9.46      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.25/9.46         (~ (r1_tarski @ X32 @ X33)
% 9.25/9.46          | ((k9_relat_1 @ (k7_relat_1 @ X34 @ X33) @ X32)
% 9.25/9.46              = (k9_relat_1 @ X34 @ X32))
% 9.25/9.46          | ~ (v1_relat_1 @ X34))),
% 9.25/9.46      inference('cnf', [status(esa)], [t162_relat_1])).
% 9.25/9.46  thf('119', plain,
% 9.25/9.46      (![X0 : $i, X1 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X1)
% 9.25/9.46          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 9.25/9.46              = (k9_relat_1 @ X1 @ X0)))),
% 9.25/9.46      inference('sup-', [status(thm)], ['117', '118'])).
% 9.25/9.46  thf('120', plain,
% 9.25/9.46      (![X29 : $i, X30 : $i]:
% 9.25/9.46         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k7_relat_1 @ X29 @ X30)))),
% 9.25/9.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 9.25/9.46  thf('121', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('demod', [status(thm)], ['87', '88'])).
% 9.25/9.46  thf(t146_relat_1, axiom,
% 9.25/9.46    (![A:$i]:
% 9.25/9.46     ( ( v1_relat_1 @ A ) =>
% 9.25/9.46       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 9.25/9.46  thf('122', plain,
% 9.25/9.46      (![X31 : $i]:
% 9.25/9.46         (((k9_relat_1 @ X31 @ (k1_relat_1 @ X31)) = (k2_relat_1 @ X31))
% 9.25/9.46          | ~ (v1_relat_1 @ X31))),
% 9.25/9.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 9.25/9.46  thf('123', plain,
% 9.25/9.46      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 9.25/9.46          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 9.25/9.46        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('sup+', [status(thm)], ['121', '122'])).
% 9.25/9.46  thf('124', plain,
% 9.25/9.46      ((~ (v1_relat_1 @ sk_B)
% 9.25/9.46        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 9.25/9.46            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 9.25/9.46      inference('sup-', [status(thm)], ['120', '123'])).
% 9.25/9.46  thf('125', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('126', plain,
% 9.25/9.46      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 9.25/9.46         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('demod', [status(thm)], ['124', '125'])).
% 9.25/9.46  thf('127', plain,
% 9.25/9.46      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 9.25/9.46        | ~ (v1_relat_1 @ sk_B))),
% 9.25/9.46      inference('sup+', [status(thm)], ['119', '126'])).
% 9.25/9.46  thf('128', plain, ((v1_relat_1 @ sk_B)),
% 9.25/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.25/9.46  thf('129', plain,
% 9.25/9.46      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('demod', [status(thm)], ['127', '128'])).
% 9.25/9.46  thf('130', plain,
% 9.25/9.46      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 9.25/9.46      inference('demod', [status(thm)], ['116', '129'])).
% 9.25/9.46  thf('131', plain, ($false), inference('demod', [status(thm)], ['0', '130'])).
% 9.25/9.46  
% 9.25/9.46  % SZS output end Refutation
% 9.25/9.46  
% 9.25/9.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
