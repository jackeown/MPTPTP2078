%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A7nF3eYzeN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 628 expanded)
%              Number of leaves         :   27 ( 234 expanded)
%              Depth                    :   19
%              Number of atoms          :  852 (5278 expanded)
%              Number of equality atoms :   66 ( 476 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X15 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X20 @ X19 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = ( k3_xboole_0 @ X26 @ ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X29 @ X28 ) @ X30 )
      | ( r1_tarski @ X28 @ ( k10_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k3_xboole_0 @ X23 @ ( k10_relat_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('64',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','56','61','62','63','64'])).

thf('66',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A7nF3eYzeN
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 856 iterations in 0.668s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.91/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.12  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.91/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.12  thf(t139_funct_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ C ) =>
% 0.91/1.12       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.91/1.12         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.12         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.91/1.12            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.91/1.12          | ~ (v1_relat_1 @ X24))),
% 0.91/1.12      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.91/1.12  thf(t175_funct_2, conjecture,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.12       ( ![B:$i,C:$i]:
% 0.91/1.12         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.91/1.12           ( ( k10_relat_1 @ A @ C ) =
% 0.91/1.12             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i]:
% 0.91/1.12        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.12          ( ![B:$i,C:$i]:
% 0.91/1.12            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.91/1.12              ( ( k10_relat_1 @ A @ C ) =
% 0.91/1.12                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.91/1.12  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(t71_relat_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.91/1.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.12  thf('2', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.91/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.12  thf(t167_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.91/1.12  thf('3', plain,
% 0.91/1.12      (![X15 : $i, X16 : $i]:
% 0.91/1.12         ((r1_tarski @ (k10_relat_1 @ X15 @ X16) @ (k1_relat_1 @ X15))
% 0.91/1.12          | ~ (v1_relat_1 @ X15))),
% 0.91/1.12      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.91/1.12  thf('4', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.12  thf(fc3_funct_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.91/1.12       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.91/1.12  thf('5', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.91/1.12      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.12  thf('7', plain,
% 0.91/1.12      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.12         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.91/1.12            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.91/1.12          | ~ (v1_relat_1 @ X24))),
% 0.91/1.12      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.91/1.12  thf(t148_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.91/1.12  thf('8', plain,
% 0.91/1.12      (![X13 : $i, X14 : $i]:
% 0.91/1.12         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.91/1.12          | ~ (v1_relat_1 @ X13))),
% 0.91/1.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.91/1.12  thf(t43_funct_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.91/1.12       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      (![X31 : $i, X32 : $i]:
% 0.91/1.12         ((k5_relat_1 @ (k6_relat_1 @ X32) @ (k6_relat_1 @ X31))
% 0.91/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X31 @ X32)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.91/1.12  thf(t94_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      (![X19 : $i, X20 : $i]:
% 0.91/1.12         (((k7_relat_1 @ X20 @ X19) = (k5_relat_1 @ (k6_relat_1 @ X19) @ X20))
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.12            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.91/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['9', '10'])).
% 0.91/1.12  thf('12', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.12  thf('13', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.12      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.12  thf('14', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.91/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.12  thf('15', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.91/1.12           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.12  thf('16', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 0.91/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['8', '15'])).
% 0.91/1.12  thf('17', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['16', '17'])).
% 0.91/1.12  thf(t148_funct_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.12       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.91/1.12         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (![X26 : $i, X27 : $i]:
% 0.91/1.12         (((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26))
% 0.91/1.12            = (k3_xboole_0 @ X26 @ (k9_relat_1 @ X27 @ (k1_relat_1 @ X27))))
% 0.91/1.12          | ~ (v1_funct_1 @ X27)
% 0.91/1.12          | ~ (v1_relat_1 @ X27))),
% 0.91/1.12      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.91/1.12            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.12            = (k3_xboole_0 @ X1 @ 
% 0.91/1.12               (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.91/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.12          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.12  thf('21', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['16', '17'])).
% 0.91/1.12  thf('22', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.91/1.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.12  thf(idempotence_k3_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.91/1.12  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.12  thf('24', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.12  thf('25', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.12           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.91/1.12  thf('27', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0)
% 0.91/1.12            = (k3_xboole_0 @ X0 @ X1))
% 0.91/1.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['7', '26'])).
% 0.91/1.12  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.12           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.12      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.12  thf('31', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.12  thf('32', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.12      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.12      inference('demod', [status(thm)], ['6', '32'])).
% 0.91/1.12  thf('34', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.91/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.13  thf(t163_funct_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.13       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.91/1.13           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.91/1.13         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.91/1.13  thf('35', plain,
% 0.91/1.13      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.91/1.13          | ~ (r1_tarski @ (k9_relat_1 @ X29 @ X28) @ X30)
% 0.91/1.13          | (r1_tarski @ X28 @ (k10_relat_1 @ X29 @ X30))
% 0.91/1.13          | ~ (v1_funct_1 @ X29)
% 0.91/1.13          | ~ (v1_relat_1 @ X29))),
% 0.91/1.13      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.91/1.13  thf('36', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X1 @ X0)
% 0.91/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.91/1.13          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.91/1.13          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.91/1.13          | ~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2))),
% 0.91/1.13      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.13  thf('37', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.13  thf('38', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.13  thf('39', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['16', '17'])).
% 0.91/1.13  thf('40', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X1 @ X0)
% 0.91/1.13          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.91/1.13          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 0.91/1.13      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.91/1.13  thf('41', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.91/1.13  thf('42', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X1 @ X0)
% 0.91/1.13          | (r1_tarski @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.91/1.13          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 0.91/1.13      inference('demod', [status(thm)], ['40', '41'])).
% 0.91/1.13  thf('43', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['33', '42'])).
% 0.91/1.13  thf('44', plain,
% 0.91/1.13      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.91/1.13        (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.91/1.13      inference('sup-', [status(thm)], ['1', '43'])).
% 0.91/1.13  thf('45', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.91/1.13  thf('46', plain,
% 0.91/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.13         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.91/1.13            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.91/1.13          | ~ (v1_relat_1 @ X24))),
% 0.91/1.13      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.91/1.13  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.13      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.13  thf('48', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (((k10_relat_1 @ (k7_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 0.91/1.13            = (k10_relat_1 @ X1 @ X0))
% 0.91/1.13          | ~ (v1_relat_1 @ X1))),
% 0.91/1.13      inference('sup+', [status(thm)], ['46', '47'])).
% 0.91/1.13  thf('49', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (((k10_relat_1 @ 
% 0.91/1.13            (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.91/1.13            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.13      inference('sup+', [status(thm)], ['45', '48'])).
% 0.91/1.13  thf('50', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.91/1.13  thf('51', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.91/1.13  thf('52', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['50', '51'])).
% 0.91/1.13  thf('53', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.13           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.13      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.13  thf('54', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.13           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.13      inference('sup+', [status(thm)], ['52', '53'])).
% 0.91/1.13  thf('55', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.91/1.13           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.13      inference('demod', [status(thm)], ['11', '12'])).
% 0.91/1.13  thf('56', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.13           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['54', '55'])).
% 0.91/1.13  thf('57', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.91/1.13  thf('58', plain,
% 0.91/1.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.13         (((k10_relat_1 @ (k7_relat_1 @ X24 @ X23) @ X25)
% 0.91/1.13            = (k3_xboole_0 @ X23 @ (k10_relat_1 @ X24 @ X25)))
% 0.91/1.13          | ~ (v1_relat_1 @ X24))),
% 0.91/1.13      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.91/1.13  thf('59', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.91/1.13            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.91/1.13          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.91/1.13      inference('sup+', [status(thm)], ['57', '58'])).
% 0.91/1.13  thf('60', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.13  thf('61', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.91/1.13           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.13      inference('demod', [status(thm)], ['59', '60'])).
% 0.91/1.13  thf('62', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.13      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.13  thf('63', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.91/1.13  thf('64', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.91/1.13      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.91/1.13  thf('65', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['49', '56', '61', '62', '63', '64'])).
% 0.91/1.13  thf('66', plain,
% 0.91/1.13      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.91/1.13        (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.91/1.13      inference('demod', [status(thm)], ['44', '65'])).
% 0.91/1.13  thf('67', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.91/1.13  thf(t17_xboole_1, axiom,
% 0.91/1.13    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.13  thf('68', plain,
% 0.91/1.13      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.91/1.13      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.91/1.13  thf(d10_xboole_0, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.13  thf('69', plain,
% 0.91/1.13      (![X1 : $i, X3 : $i]:
% 0.91/1.13         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.91/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.13  thf('70', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.91/1.13          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['68', '69'])).
% 0.91/1.13  thf('71', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.13          | ((X0) = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.91/1.13      inference('sup-', [status(thm)], ['67', '70'])).
% 0.91/1.13  thf('72', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.91/1.13           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.91/1.13  thf('73', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.13          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.13      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.13  thf('74', plain,
% 0.91/1.13      (((k10_relat_1 @ sk_A @ sk_C)
% 0.91/1.13         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['66', '73'])).
% 0.91/1.13  thf('75', plain,
% 0.91/1.13      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.91/1.13          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.91/1.13        | ~ (v1_relat_1 @ sk_A))),
% 0.91/1.13      inference('sup+', [status(thm)], ['0', '74'])).
% 0.91/1.13  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('77', plain,
% 0.91/1.13      (((k10_relat_1 @ sk_A @ sk_C)
% 0.91/1.13         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.91/1.13      inference('demod', [status(thm)], ['75', '76'])).
% 0.91/1.13  thf('78', plain,
% 0.91/1.13      (((k10_relat_1 @ sk_A @ sk_C)
% 0.91/1.13         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('79', plain, ($false),
% 0.91/1.13      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.91/1.13  
% 0.91/1.13  % SZS output end Refutation
% 0.91/1.13  
% 0.91/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
