%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.apnMWw1jyY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:57 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 356 expanded)
%              Number of leaves         :   25 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          :  817 (2769 expanded)
%              Number of equality atoms :   75 ( 234 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ ( k1_relat_1 @ X33 ) )
        = X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['18','24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X30: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X30 ) )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('36',plain,(
    ! [X30: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X30 ) )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('38',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) @ X22 )
        = ( k8_relat_1 @ X20 @ ( k7_relat_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('65',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.apnMWw1jyY
% 0.16/0.38  % Computer   : n008.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:15:15 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 435 iterations in 0.233s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.46/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.68  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.68  thf(t123_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ B ) =>
% 0.46/0.68       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i]:
% 0.46/0.68         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.46/0.68          | ~ (v1_relat_1 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.46/0.68  thf(t43_funct_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.46/0.68       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i]:
% 0.46/0.68        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.46/0.68          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.46/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.46/0.68          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.46/0.68        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.68  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.68  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.46/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.68  thf(commutativity_k2_tarski, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.68  thf(t12_setfam_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i]:
% 0.46/0.68         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i]:
% 0.46/0.68         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf(t71_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.68       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.68  thf('10', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 0.46/0.68      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.68  thf(t98_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X33 : $i]:
% 0.46/0.68         (((k7_relat_1 @ X33 @ (k1_relat_1 @ X33)) = (X33))
% 0.46/0.68          | ~ (v1_relat_1 @ X33))),
% 0.46/0.68      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.68  thf('13', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf(t100_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ C ) =>
% 0.46/0.68       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.46/0.68         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k7_relat_1 @ X12 @ X13) @ X14)
% 0.46/0.68            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14)))
% 0.46/0.68          | ~ (v1_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.46/0.68            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.68  thf('17', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.46/0.68           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i]:
% 0.46/0.68         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.46/0.68          | ~ (v1_relat_1 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.46/0.68  thf(t94_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ B ) =>
% 0.46/0.68       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X31 : $i, X32 : $i]:
% 0.46/0.68         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 0.46/0.68          | ~ (v1_relat_1 @ X32))),
% 0.46/0.68      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('22', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('23', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.46/0.68           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.46/0.68      inference('demod', [status(thm)], ['18', '24', '25'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i]:
% 0.46/0.68         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.46/0.68          | ~ (v1_relat_1 @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (![X31 : $i, X32 : $i]:
% 0.46/0.68         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 0.46/0.68          | ~ (v1_relat_1 @ X32))),
% 0.46/0.68      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.46/0.68  thf(t72_relat_1, axiom,
% 0.46/0.68    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X30 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X30)) = (k6_relat_1 @ X30))),
% 0.46/0.68      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.46/0.68  thf(t54_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( v1_relat_1 @ B ) =>
% 0.46/0.68           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.46/0.68             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X23 : $i, X24 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X23)
% 0.46/0.68          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 0.46/0.68              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 0.46/0.68          | ~ (v1_relat_1 @ X24))),
% 0.46/0.68      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.46/0.68          | ~ (v1_relat_1 @ X1)
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf('32', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.46/0.68          | ~ (v1_relat_1 @ X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.46/0.68            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.46/0.68               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['28', '33'])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X30 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X30)) = (k6_relat_1 @ X30))),
% 0.46/0.68      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.46/0.68  thf('37', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('38', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.46/0.68            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['27', '39'])).
% 0.46/0.68  thf('41', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['26', '42'])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf(t140_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ C ) =>
% 0.46/0.68       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.46/0.68         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k8_relat_1 @ X20 @ X21) @ X22)
% 0.46/0.68            = (k8_relat_1 @ X20 @ (k7_relat_1 @ X21 @ X22)))
% 0.46/0.68          | ~ (v1_relat_1 @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.46/0.68            = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.68  thf('52', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.46/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.46/0.68           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['48', '53'])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.46/0.68           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.46/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ (k6_relat_1 @ X0))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.46/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['45', '56'])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.46/0.68              (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.46/0.68      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.46/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k7_relat_1 @ X12 @ X13) @ X14)
% 0.46/0.68            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14)))
% 0.46/0.68          | ~ (v1_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.46/0.68            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.46/0.68          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.68  thf('65', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.46/0.68           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.46/0.68      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.46/0.68           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['60', '66'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.46/0.68              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.68      inference('demod', [status(thm)], ['59', '67'])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.46/0.68           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.46/0.68              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['9', '68'])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.46/0.68           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.46/0.68         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['4', '71'])).
% 0.46/0.68  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
