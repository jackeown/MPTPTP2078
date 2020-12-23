%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMp5l7Ng3r

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 250 expanded)
%              Number of leaves         :   26 (  98 expanded)
%              Depth                    :   16
%              Number of atoms          :  638 (2043 expanded)
%              Number of equality atoms :   47 ( 177 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X30 @ X29 ) @ X31 )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X23 @ X22 ) @ X24 )
        = ( k3_xboole_0 @ X22 @ ( k10_relat_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X27 ) )
        = ( k3_xboole_0 @ X27 @ ( k9_relat_1 @ X28 @ ( k1_relat_1 @ X28 ) ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('28',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','36','37','38'])).

thf('40',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rMp5l7Ng3r
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:24:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 191 iterations in 0.116s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.57  thf(t139_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ C ) =>
% 0.20/0.57       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.57         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.57         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 0.20/0.57            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 0.20/0.57          | ~ (v1_relat_1 @ X23))),
% 0.20/0.57      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.57  thf(t175_funct_2, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.57       ( ![B:$i,C:$i]:
% 0.20/0.57         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.57           ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.57             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.57          ( ![B:$i,C:$i]:
% 0.20/0.57            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.57              ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.57                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.20/0.57  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t148_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i]:
% 0.20/0.57         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.57          | ~ (v1_relat_1 @ X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.57  thf(t94_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i]:
% 0.20/0.57         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.20/0.57          | ~ (v1_relat_1 @ X19))),
% 0.20/0.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.57  thf(t43_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.57       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X32 : $i, X33 : $i]:
% 0.20/0.57         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 0.20/0.57           = (k6_relat_1 @ (k3_xboole_0 @ X32 @ X33)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.57            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf(fc3_funct_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.57  thf('6', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.57           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf(t71_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.57  thf('8', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['2', '9'])).
% 0.20/0.57  thf('11', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf(d10_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('14', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.20/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.57  thf(t163_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.57       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.57           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.57         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 0.20/0.57          | ~ (r1_tarski @ (k9_relat_1 @ X30 @ X29) @ X31)
% 0.20/0.57          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ X31))
% 0.20/0.57          | ~ (v1_funct_1 @ X30)
% 0.20/0.57          | ~ (v1_relat_1 @ X30))),
% 0.20/0.57      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_1 @ X0)
% 0.20/0.57          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.57          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r1_tarski @ 
% 0.20/0.57             (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ X1)
% 0.20/0.57          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.20/0.57             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.57          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.57  thf('18', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.57  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.57  thf('20', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.57         (((k10_relat_1 @ (k7_relat_1 @ X23 @ X22) @ X24)
% 0.20/0.57            = (k3_xboole_0 @ X22 @ (k10_relat_1 @ X23 @ X24)))
% 0.20/0.57          | ~ (v1_relat_1 @ X23))),
% 0.20/0.57      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf(t148_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.57       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.20/0.57         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X27 : $i, X28 : $i]:
% 0.20/0.57         (((k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X27))
% 0.20/0.57            = (k3_xboole_0 @ X27 @ (k9_relat_1 @ X28 @ (k1_relat_1 @ X28))))
% 0.20/0.57          | ~ (v1_funct_1 @ X28)
% 0.20/0.57          | ~ (v1_relat_1 @ X28))),
% 0.20/0.57      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.57            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.57            = (k3_xboole_0 @ X1 @ 
% 0.20/0.57               (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.20/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.57          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf('26', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.57  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.57  thf('28', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('29', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27', '28', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0)
% 0.20/0.57            = (k3_xboole_0 @ X0 @ X1))
% 0.20/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['21', '30'])).
% 0.20/0.57  thf('32', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.57           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.57  thf('35', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['31', '34', '35'])).
% 0.20/0.57  thf('37', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('38', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)],
% 0.20/0.57                ['17', '18', '19', '20', '36', '37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.20/0.57        (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27', '28', '29'])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf(t145_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.57       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (![X25 : $i, X26 : $i]:
% 0.20/0.57         ((r1_tarski @ (k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X26)) @ X26)
% 0.20/0.57          | ~ (v1_funct_1 @ X25)
% 0.20/0.57          | ~ (v1_relat_1 @ X25))),
% 0.20/0.57      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r1_tarski @ 
% 0.20/0.57           (k3_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)
% 0.20/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.20/0.57          | ~ (v1_funct_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('45', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('46', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (r1_tarski @ 
% 0.20/0.57          (k3_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)),
% 0.20/0.57      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27', '28', '29'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.57      inference('sup+', [status(thm)], ['41', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X1 : $i, X3 : $i]:
% 0.20/0.57         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.57         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['40', '52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.57          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['0', '53'])).
% 0.20/0.57  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.57         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (((k10_relat_1 @ sk_A @ sk_C)
% 0.20/0.57         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('58', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
