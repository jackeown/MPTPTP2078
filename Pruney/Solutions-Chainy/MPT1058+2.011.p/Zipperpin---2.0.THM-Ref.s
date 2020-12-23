%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vASxLtLZOj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:38 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 292 expanded)
%              Number of leaves         :   34 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  768 (2169 expanded)
%              Number of equality atoms :   67 ( 230 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

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

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X29 @ X28 ) @ X30 )
      | ( r1_tarski @ X28 @ ( k10_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('39',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','37','38','39','40'])).

thf('42',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('53',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = ( k3_xboole_0 @ X26 @ ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('66',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vASxLtLZOj
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:03:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 289 iterations in 0.115s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(t139_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ C ) =>
% 0.39/0.56       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.39/0.56         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.56         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.39/0.56            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.39/0.56          | ~ (v1_relat_1 @ X24))),
% 0.39/0.56      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.39/0.56  thf(t175_funct_2, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.56       ( ![B:$i,C:$i]:
% 0.39/0.56         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.39/0.56           ( ( k10_relat_1 @ A @ C ) =
% 0.39/0.56             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.56          ( ![B:$i,C:$i]:
% 0.39/0.56            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.39/0.56              ( ( k10_relat_1 @ A @ C ) =
% 0.39/0.56                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.39/0.56  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t71_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.56  thf('2', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf(d10_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.39/0.56  thf(t163_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.56       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.39/0.56           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.39/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.39/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X29 @ X28) @ X30)
% 0.39/0.56          | (r1_tarski @ X28 @ (k10_relat_1 @ X29 @ X30))
% 0.39/0.56          | ~ (v1_funct_1 @ X29)
% 0.39/0.56          | ~ (v1_relat_1 @ X29))),
% 0.39/0.56      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X0)
% 0.39/0.56          | ~ (v1_funct_1 @ X0)
% 0.39/0.56          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.39/0.56          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.39/0.56             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '6'])).
% 0.39/0.56  thf(t3_boole, axiom,
% 0.39/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.56  thf('8', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.56  thf(t48_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.39/0.56  thf(commutativity_k2_tarski, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.56  thf(t12_setfam_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['10', '15'])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.56  thf(t36_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.39/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.56  thf(t3_xboole_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['17', '20'])).
% 0.39/0.56  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['16', '21'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.56  thf('25', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.56  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.56  thf(t94_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 0.39/0.56          | ~ (v1_relat_1 @ X20))),
% 0.39/0.56      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.39/0.56  thf(t43_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.39/0.56       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.56  thf('28', plain,
% 0.39/0.56      (![X31 : $i, X32 : $i]:
% 0.39/0.56         ((k5_relat_1 @ (k6_relat_1 @ X32) @ (k6_relat_1 @ X31))
% 0.39/0.56           = (k6_relat_1 @ (k3_xboole_0 @ X31 @ X32)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.56            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.56  thf(fc3_funct_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.39/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.56  thf('30', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.39/0.56           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['26', '31'])).
% 0.39/0.56  thf(t148_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (![X15 : $i, X16 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.39/0.56          | ~ (v1_relat_1 @ X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.56            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['32', '33'])).
% 0.39/0.56  thf('35', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf('36', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.56  thf('38', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf('39', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('40', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.56          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['7', '37', '38', '39', '40'])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.39/0.56        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '41'])).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['26', '31'])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.56         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.39/0.56            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.39/0.56          | ~ (v1_relat_1 @ X24))),
% 0.39/0.56      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.56  thf('46', plain,
% 0.39/0.56      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.39/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.56  thf('47', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.39/0.56      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 0.39/0.56          | ~ (v1_relat_1 @ X2))),
% 0.39/0.56      inference('sup+', [status(thm)], ['44', '47'])).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      (![X0 : $i, X2 : $i]:
% 0.39/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X2)
% 0.39/0.56          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 0.39/0.56          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56          | ((X0) = (k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '50'])).
% 0.39/0.56  thf('52', plain,
% 0.39/0.56      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['26', '31'])).
% 0.39/0.56  thf('53', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.39/0.56  thf('55', plain,
% 0.39/0.56      (((k10_relat_1 @ sk_A @ sk_C)
% 0.39/0.56         = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '54'])).
% 0.39/0.56  thf('56', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf(t148_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.56       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.39/0.56         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.39/0.56  thf('57', plain,
% 0.39/0.56      (![X26 : $i, X27 : $i]:
% 0.39/0.56         (((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26))
% 0.39/0.56            = (k3_xboole_0 @ X26 @ (k9_relat_1 @ X27 @ (k1_relat_1 @ X27))))
% 0.39/0.56          | ~ (v1_funct_1 @ X27)
% 0.39/0.56          | ~ (v1_relat_1 @ X27))),
% 0.39/0.56      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.39/0.56  thf('58', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.39/0.56            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56            = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.56  thf('59', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('60', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.56  thf('61', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.39/0.56           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56           = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.39/0.56      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.39/0.56  thf('62', plain,
% 0.39/0.56      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.56  thf('63', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.39/0.56           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (k3_xboole_0 @ X1 @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.39/0.56  thf('64', plain,
% 0.39/0.56      (((k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.39/0.56         (k10_relat_1 @ sk_A @ sk_C))
% 0.39/0.56         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['55', '63'])).
% 0.39/0.56  thf('65', plain,
% 0.39/0.56      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.56  thf('66', plain,
% 0.39/0.56      (((k10_relat_1 @ sk_A @ sk_C)
% 0.39/0.56         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.39/0.56  thf('67', plain,
% 0.39/0.56      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.39/0.56          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_A))),
% 0.39/0.56      inference('sup+', [status(thm)], ['0', '66'])).
% 0.39/0.56  thf('68', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('69', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.39/0.57         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.39/0.57         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('71', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
