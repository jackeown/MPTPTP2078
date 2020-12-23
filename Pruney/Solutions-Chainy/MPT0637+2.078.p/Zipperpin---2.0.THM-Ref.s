%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V1zhZRwpE3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:07 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  238 (14427 expanded)
%              Number of leaves         :   30 (5364 expanded)
%              Depth                    :   26
%              Number of atoms          : 2276 (118427 expanded)
%              Number of equality atoms :  170 (9310 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X21 ) @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('19',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','17','18','19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','17','18','19','20'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('32',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k8_relat_1 @ X18 @ X17 )
        = ( k3_xboole_0 @ X17 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('42',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('44',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','40','41','42','43','44','45'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('47',plain,(
    ! [X36: $i] :
      ( ( ( k7_relat_1 @ X36 @ ( k1_relat_1 @ X36 ) )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','40','41','42','43','44','45'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('61',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('71',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('78',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k5_relat_1 @ X24 @ ( k5_relat_1 @ X23 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('94',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('95',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97'])).

thf('99',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('100',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      = ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('112',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('121',plain,(
    ! [X31: $i] :
      ( ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X2 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['119','132'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('135',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('136',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( ( k5_relat_1 @ X29 @ ( k6_relat_1 @ X30 ) )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('144',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('145',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','75'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['155','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['119','132'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('166',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ X35 @ X34 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('167',plain,(
    ! [X28: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('168',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X21 ) @ ( k4_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['166','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('175',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['173','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k7_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X2 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['165','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) ) ) ) @ X2 ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['164','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) ) ) @ X1 ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) @ X2 ) ),
    inference('sup+',[status(thm)],['163','187'])).

thf('189',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['162','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','17','18','19','20'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['161','197'])).

thf('199',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','152'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['161','197'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['161','197'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','204'])).

thf('206',plain,(
    $false ),
    inference(simplify,[status(thm)],['205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V1zhZRwpE3
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.08  % Solved by: fo/fo7.sh
% 0.89/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.08  % done 1112 iterations in 0.624s
% 0.89/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.08  % SZS output start Refutation
% 0.89/1.08  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.89/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.08  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.89/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.08  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.89/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.08  thf(t123_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.89/1.08  thf('0', plain,
% 0.89/1.08      (![X15 : $i, X16 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.08          | ~ (v1_relat_1 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.08  thf(t43_funct_1, conjecture,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.89/1.08       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.89/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.08    (~( ![A:$i,B:$i]:
% 0.89/1.08        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.89/1.08          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.89/1.08    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.89/1.08  thf('1', plain,
% 0.89/1.08      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.89/1.08         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('2', plain,
% 0.89/1.08      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.89/1.08          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.89/1.08        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.08  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.89/1.08  thf('3', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('4', plain,
% 0.89/1.08      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.89/1.08         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf(t94_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.89/1.08  thf('5', plain,
% 0.89/1.08      (![X34 : $i, X35 : $i]:
% 0.89/1.08         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 0.89/1.08          | ~ (v1_relat_1 @ X35))),
% 0.89/1.08      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.08  thf(t72_relat_1, axiom,
% 0.89/1.08    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.08  thf('6', plain,
% 0.89/1.08      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.08  thf(t54_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( v1_relat_1 @ B ) =>
% 0.89/1.08           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.89/1.08             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.08  thf('7', plain,
% 0.89/1.08      (![X21 : $i, X22 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X21)
% 0.89/1.08          | ((k4_relat_1 @ (k5_relat_1 @ X22 @ X21))
% 0.89/1.08              = (k5_relat_1 @ (k4_relat_1 @ X21) @ (k4_relat_1 @ X22)))
% 0.89/1.08          | ~ (v1_relat_1 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.89/1.08  thf('8', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.08  thf('9', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('10', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.89/1.08          | ~ (v1_relat_1 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['8', '9'])).
% 0.89/1.08  thf('11', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.08               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['5', '10'])).
% 0.89/1.08  thf('12', plain,
% 0.89/1.08      (![X15 : $i, X16 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.08          | ~ (v1_relat_1 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.08  thf('13', plain,
% 0.89/1.08      (![X34 : $i, X35 : $i]:
% 0.89/1.08         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 0.89/1.08          | ~ (v1_relat_1 @ X35))),
% 0.89/1.08      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.08  thf('14', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.08            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.89/1.08  thf('15', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('16', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('17', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.89/1.08  thf('18', plain,
% 0.89/1.08      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.08  thf('19', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('20', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('21', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['11', '17', '18', '19', '20'])).
% 0.89/1.08  thf('22', plain,
% 0.89/1.08      (![X15 : $i, X16 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.08          | ~ (v1_relat_1 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.08  thf('23', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['11', '17', '18', '19', '20'])).
% 0.89/1.08  thf('24', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['22', '23'])).
% 0.89/1.08  thf('25', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('26', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.08  thf('27', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf(t45_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( v1_relat_1 @ B ) =>
% 0.89/1.08           ( r1_tarski @
% 0.89/1.08             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.89/1.08  thf('28', plain,
% 0.89/1.08      (![X19 : $i, X20 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X19)
% 0.89/1.08          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.89/1.08             (k2_relat_1 @ X19))
% 0.89/1.08          | ~ (v1_relat_1 @ X20))),
% 0.89/1.08      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.89/1.08  thf(t79_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.89/1.08         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.89/1.08  thf('29', plain,
% 0.89/1.08      (![X29 : $i, X30 : $i]:
% 0.89/1.08         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.89/1.08          | ((k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) = (X29))
% 0.89/1.08          | ~ (v1_relat_1 @ X29))),
% 0.89/1.08      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.89/1.08  thf('30', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ X0)
% 0.89/1.08          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.08          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 0.89/1.08              (k6_relat_1 @ (k2_relat_1 @ X0))) = (k5_relat_1 @ X1 @ X0)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['28', '29'])).
% 0.89/1.08  thf('31', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ((k5_relat_1 @ 
% 0.89/1.08              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)) @ 
% 0.89/1.08              (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X1))))
% 0.89/1.08              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['27', '30'])).
% 0.89/1.08  thf(t71_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.08  thf('32', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.89/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.08  thf(t124_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ( k8_relat_1 @ A @ B ) =
% 0.89/1.08         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.89/1.08  thf('33', plain,
% 0.89/1.08      (![X17 : $i, X18 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X18 @ X17)
% 0.89/1.08            = (k3_xboole_0 @ X17 @ (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ X18)))
% 0.89/1.08          | ~ (v1_relat_1 @ X17))),
% 0.89/1.08      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.89/1.08  thf('34', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.08            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['32', '33'])).
% 0.89/1.08  thf('35', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('36', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.08           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.89/1.08      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.08  thf(fc1_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.89/1.08  thf('37', plain,
% 0.89/1.08      (![X10 : $i, X11 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.89/1.08      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.89/1.08  thf('38', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['36', '37'])).
% 0.89/1.08  thf('39', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('40', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('41', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('42', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.89/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.08  thf('43', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('44', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('45', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('46', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.89/1.08           (k6_relat_1 @ X1)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)],
% 0.89/1.08                ['31', '40', '41', '42', '43', '44', '45'])).
% 0.89/1.08  thf(t98_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) =>
% 0.89/1.08       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.08  thf('47', plain,
% 0.89/1.08      (![X36 : $i]:
% 0.89/1.08         (((k7_relat_1 @ X36 @ (k1_relat_1 @ X36)) = (X36))
% 0.89/1.08          | ~ (v1_relat_1 @ X36))),
% 0.89/1.08      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.89/1.08  thf(t112_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ![C:$i]:
% 0.89/1.08         ( ( v1_relat_1 @ C ) =>
% 0.89/1.08           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.89/1.08             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.89/1.08  thf('48', plain,
% 0.89/1.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X12)
% 0.89/1.08          | ((k7_relat_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 0.89/1.08              = (k5_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X12))
% 0.89/1.08          | ~ (v1_relat_1 @ X13))),
% 0.89/1.08      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.89/1.08  thf('49', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k7_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.89/1.08            = (k5_relat_1 @ X0 @ X1))
% 0.89/1.08          | ~ (v1_relat_1 @ X0)
% 0.89/1.08          | ~ (v1_relat_1 @ X0)
% 0.89/1.08          | ~ (v1_relat_1 @ X1))),
% 0.89/1.08      inference('sup+', [status(thm)], ['47', '48'])).
% 0.89/1.08  thf('50', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ X0)
% 0.89/1.08          | ((k7_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.89/1.08              = (k5_relat_1 @ X0 @ X1)))),
% 0.89/1.08      inference('simplify', [status(thm)], ['49'])).
% 0.89/1.08  thf('51', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.89/1.08            (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.89/1.08            = (k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.89/1.08               (k6_relat_1 @ X1)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['46', '50'])).
% 0.89/1.08  thf('52', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.89/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.08  thf(t90_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.89/1.08         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.89/1.08  thf('53', plain,
% 0.89/1.08      (![X32 : $i, X33 : $i]:
% 0.89/1.08         (((k1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 0.89/1.08            = (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33))
% 0.89/1.08          | ~ (v1_relat_1 @ X32))),
% 0.89/1.08      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.89/1.08  thf('54', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.08            = (k3_xboole_0 @ X0 @ X1))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.08  thf('55', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('56', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.08           = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.08  thf('57', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.89/1.08  thf('58', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.08  thf('59', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k5_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.89/1.08           (k6_relat_1 @ X1)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)],
% 0.89/1.08                ['31', '40', '41', '42', '43', '44', '45'])).
% 0.89/1.08  thf('60', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('61', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('62', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 0.89/1.08           (k3_xboole_0 @ X1 @ X0)) = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['51', '58', '59', '60', '61'])).
% 0.89/1.08  thf('63', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.89/1.08  thf('64', plain,
% 0.89/1.08      (![X15 : $i, X16 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.08          | ~ (v1_relat_1 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.08  thf('65', plain,
% 0.89/1.08      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X12)
% 0.89/1.08          | ((k7_relat_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 0.89/1.08              = (k5_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X12))
% 0.89/1.08          | ~ (v1_relat_1 @ X13))),
% 0.89/1.08      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.89/1.08  thf('66', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.89/1.08            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['64', '65'])).
% 0.89/1.08  thf('67', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('68', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.89/1.08            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['66', '67'])).
% 0.89/1.08  thf('69', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.08          | ((k7_relat_1 @ 
% 0.89/1.08              (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)) @ X0)
% 0.89/1.08              = (k8_relat_1 @ X2 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['63', '68'])).
% 0.89/1.08  thf('70', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('71', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('72', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.89/1.08  thf('73', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)) @ 
% 0.89/1.08           X0) = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.08      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.89/1.08  thf('74', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('75', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.08      inference('demod', [status(thm)], ['73', '74'])).
% 0.89/1.08  thf('76', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X1 @ 
% 0.89/1.08           (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['62', '75'])).
% 0.89/1.08  thf('77', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('78', plain,
% 0.89/1.08      (![X34 : $i, X35 : $i]:
% 0.89/1.08         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 0.89/1.08          | ~ (v1_relat_1 @ X35))),
% 0.89/1.08      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.08  thf(t55_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( v1_relat_1 @ B ) =>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( v1_relat_1 @ C ) =>
% 0.89/1.08               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.89/1.08                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf('79', plain,
% 0.89/1.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X23)
% 0.89/1.08          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.89/1.08              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 0.89/1.08          | ~ (v1_relat_1 @ X25)
% 0.89/1.08          | ~ (v1_relat_1 @ X24))),
% 0.89/1.08      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.89/1.08  thf('80', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ X2)
% 0.89/1.08          | ~ (v1_relat_1 @ X1))),
% 0.89/1.08      inference('sup+', [status(thm)], ['78', '79'])).
% 0.89/1.08  thf('81', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('82', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ X2)
% 0.89/1.08          | ~ (v1_relat_1 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['80', '81'])).
% 0.89/1.08  thf('83', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X2)
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.89/1.08              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 0.89/1.08      inference('simplify', [status(thm)], ['82'])).
% 0.89/1.08  thf('84', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2) @ 
% 0.89/1.08            (k6_relat_1 @ X1))
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.89/1.08               (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['77', '83'])).
% 0.89/1.08  thf('85', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.89/1.08  thf('86', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('87', plain,
% 0.89/1.08      (![X15 : $i, X16 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.08          | ~ (v1_relat_1 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.08  thf('88', plain,
% 0.89/1.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X23)
% 0.89/1.08          | ((k5_relat_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.89/1.08              = (k5_relat_1 @ X24 @ (k5_relat_1 @ X23 @ X25)))
% 0.89/1.08          | ~ (v1_relat_1 @ X25)
% 0.89/1.08          | ~ (v1_relat_1 @ X24))),
% 0.89/1.08      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.89/1.08  thf('89', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.08            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.89/1.08          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.89/1.08          | ~ (v1_relat_1 @ X0))),
% 0.89/1.08      inference('sup+', [status(thm)], ['87', '88'])).
% 0.89/1.08  thf('90', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('91', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.08            = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.89/1.08          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ X1)
% 0.89/1.08          | ~ (v1_relat_1 @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['89', '90'])).
% 0.89/1.08  thf('92', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.08          | ((k8_relat_1 @ X2 @ 
% 0.89/1.08              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.89/1.08              = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.08                 (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X2)))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['86', '91'])).
% 0.89/1.08  thf('93', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('94', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('95', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('96', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('97', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.08  thf('98', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.08              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.89/1.08      inference('demod', [status(thm)], ['92', '93', '94', '95', '96', '97'])).
% 0.89/1.08  thf('99', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('100', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('101', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k5_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2)) @ 
% 0.89/1.08           (k6_relat_1 @ X1))
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2))))),
% 0.89/1.08      inference('demod', [status(thm)], ['84', '85', '98', '99', '100'])).
% 0.89/1.08  thf('102', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.89/1.08          | ~ (v1_relat_1 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['8', '9'])).
% 0.89/1.08  thf('103', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k4_relat_1 @ 
% 0.89/1.08            (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.89/1.08            = (k5_relat_1 @ (k6_relat_1 @ X2) @ 
% 0.89/1.08               (k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))))
% 0.89/1.08          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['101', '102'])).
% 0.89/1.08  thf('104', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.08  thf('105', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.89/1.08              (k8_relat_1 @ X2 @ (k6_relat_1 @ X1))))),
% 0.89/1.08      inference('demod', [status(thm)], ['92', '93', '94', '95', '96', '97'])).
% 0.89/1.08  thf('106', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('107', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k4_relat_1 @ 
% 0.89/1.08           (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.89/1.08           = (k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X2))))),
% 0.89/1.08      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.89/1.08  thf('108', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.89/1.08              (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['76', '107'])).
% 0.89/1.08  thf('109', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.08  thf('110', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.08           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.89/1.08              (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.89/1.08      inference('demod', [status(thm)], ['108', '109'])).
% 0.89/1.08  thf('111', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.08  thf('112', plain,
% 0.89/1.08      (![X32 : $i, X33 : $i]:
% 0.89/1.08         (((k1_relat_1 @ (k7_relat_1 @ X32 @ X33))
% 0.89/1.08            = (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33))
% 0.89/1.08          | ~ (v1_relat_1 @ X32))),
% 0.89/1.08      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.89/1.08  thf('113', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k1_relat_1 @ 
% 0.89/1.08            (k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2))
% 0.89/1.08            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.89/1.08          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['111', '112'])).
% 0.89/1.08  thf('114', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.89/1.08           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.08      inference('demod', [status(thm)], ['73', '74'])).
% 0.89/1.08  thf('115', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('116', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k1_relat_1 @ 
% 0.89/1.08           (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.89/1.08      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.89/1.08  thf('117', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1) @ X0))),
% 0.89/1.08      inference('sup+', [status(thm)], ['110', '116'])).
% 0.89/1.08  thf('118', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.08  thf('119', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k3_xboole_0 @ X1 @ X0)
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1) @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['117', '118'])).
% 0.89/1.08  thf('120', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.89/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.08  thf(t80_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) =>
% 0.89/1.08       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.89/1.08  thf('121', plain,
% 0.89/1.08      (![X31 : $i]:
% 0.89/1.08         (((k5_relat_1 @ X31 @ (k6_relat_1 @ (k2_relat_1 @ X31))) = (X31))
% 0.89/1.08          | ~ (v1_relat_1 @ X31))),
% 0.89/1.08      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.89/1.08  thf('122', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.08            = (k6_relat_1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['120', '121'])).
% 0.89/1.08  thf('123', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('124', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.89/1.08           = (k6_relat_1 @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['122', '123'])).
% 0.89/1.08  thf('125', plain,
% 0.89/1.08      (![X15 : $i, X16 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.08          | ~ (v1_relat_1 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.08  thf('126', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.89/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['124', '125'])).
% 0.89/1.08  thf('127', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.08  thf('128', plain,
% 0.89/1.08      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['126', '127'])).
% 0.89/1.08  thf('129', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         ((k1_relat_1 @ 
% 0.89/1.08           (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X2))))
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.89/1.08      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.89/1.08  thf('130', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.89/1.08      inference('sup+', [status(thm)], ['128', '129'])).
% 0.89/1.08  thf('131', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.08           = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.08      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.08  thf('132', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k3_xboole_0 @ X1 @ X0)
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['130', '131'])).
% 0.89/1.08  thf('133', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k3_xboole_0 @ X1 @ X0)
% 0.89/1.08           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['119', '132'])).
% 0.89/1.08  thf(t17_xboole_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.89/1.08  thf('134', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.89/1.08      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.89/1.08  thf('135', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.09  thf('136', plain,
% 0.89/1.09      (![X29 : $i, X30 : $i]:
% 0.89/1.09         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.89/1.09          | ((k5_relat_1 @ X29 @ (k6_relat_1 @ X30)) = (X29))
% 0.89/1.09          | ~ (v1_relat_1 @ X29))),
% 0.89/1.09      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.89/1.09  thf('137', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.09              = (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['135', '136'])).
% 0.89/1.09  thf('138', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.09  thf('139', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.09          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.09              = (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['137', '138'])).
% 0.89/1.09  thf('140', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.89/1.09           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['134', '139'])).
% 0.89/1.09  thf('141', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.09            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.89/1.09          | ~ (v1_relat_1 @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['8', '9'])).
% 0.89/1.09  thf('142', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.09               (k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))))
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['140', '141'])).
% 0.89/1.09  thf('143', plain,
% 0.89/1.09      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.89/1.09      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.09  thf('144', plain,
% 0.89/1.09      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.89/1.09      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.09  thf('145', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.09  thf('146', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.89/1.09           = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.89/1.09              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.89/1.09      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.89/1.09  thf('147', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.09           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.09  thf('148', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.89/1.09           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('demod', [status(thm)], ['146', '147'])).
% 0.89/1.09  thf('149', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.09           = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.09  thf('150', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['148', '149'])).
% 0.89/1.09  thf('151', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.89/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.09  thf('152', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k3_xboole_0 @ X1 @ X0)
% 0.89/1.09           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['150', '151'])).
% 0.89/1.09  thf('153', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['133', '152'])).
% 0.89/1.09  thf('154', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ 
% 0.89/1.09           (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.89/1.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['62', '75'])).
% 0.89/1.09  thf('155', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X0 @ 
% 0.89/1.09           (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.89/1.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['153', '154'])).
% 0.89/1.09  thf('156', plain,
% 0.89/1.09      (![X15 : $i, X16 : $i]:
% 0.89/1.09         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.89/1.09          | ~ (v1_relat_1 @ X15))),
% 0.89/1.09      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.89/1.09  thf('157', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.89/1.09           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['134', '139'])).
% 0.89/1.09  thf('158', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['156', '157'])).
% 0.89/1.09  thf('159', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.09  thf('160', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['158', '159'])).
% 0.89/1.09  thf('161', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('demod', [status(thm)], ['155', '160'])).
% 0.89/1.09  thf('162', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k3_xboole_0 @ X1 @ X0)
% 0.89/1.09           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['119', '132'])).
% 0.89/1.09  thf('163', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['158', '159'])).
% 0.89/1.09  thf('164', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.89/1.09           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1)))),
% 0.89/1.09      inference('demod', [status(thm)], ['146', '147'])).
% 0.89/1.09  thf('165', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf('166', plain,
% 0.89/1.09      (![X34 : $i, X35 : $i]:
% 0.89/1.09         (((k7_relat_1 @ X35 @ X34) = (k5_relat_1 @ (k6_relat_1 @ X34) @ X35))
% 0.89/1.09          | ~ (v1_relat_1 @ X35))),
% 0.89/1.09      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.89/1.09  thf('167', plain,
% 0.89/1.09      (![X28 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.89/1.09      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.89/1.09  thf('168', plain,
% 0.89/1.09      (![X21 : $i, X22 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ X21)
% 0.89/1.09          | ((k4_relat_1 @ (k5_relat_1 @ X22 @ X21))
% 0.89/1.09              = (k5_relat_1 @ (k4_relat_1 @ X21) @ (k4_relat_1 @ X22)))
% 0.89/1.09          | ~ (v1_relat_1 @ X22))),
% 0.89/1.09      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.89/1.09  thf('169', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.09            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.09          | ~ (v1_relat_1 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['167', '168'])).
% 0.89/1.09  thf('170', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.09  thf('171', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.09            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['169', '170'])).
% 0.89/1.09  thf('172', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((k4_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.89/1.09            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ~ (v1_relat_1 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['166', '171'])).
% 0.89/1.09  thf('173', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ X1)
% 0.89/1.09          | ((k4_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.89/1.09              = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_relat_1 @ X0))))),
% 0.89/1.09      inference('simplify', [status(thm)], ['172'])).
% 0.89/1.09  thf('174', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.09  thf('175', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ X19)
% 0.89/1.09          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.89/1.09             (k2_relat_1 @ X19))
% 0.89/1.09          | ~ (v1_relat_1 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.89/1.09  thf('176', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.89/1.09           X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['174', '175'])).
% 0.89/1.09  thf('177', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.89/1.09  thf('178', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.89/1.09           X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X1))),
% 0.89/1.09      inference('demod', [status(thm)], ['176', '177'])).
% 0.89/1.09  thf('179', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.89/1.09           X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X1)
% 0.89/1.09          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['173', '178'])).
% 0.89/1.09  thf('180', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.09          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.09          | (r1_tarski @ 
% 0.89/1.09             (k2_relat_1 @ 
% 0.89/1.09              (k4_relat_1 @ 
% 0.89/1.09               (k7_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X2))) @ 
% 0.89/1.09             X2))),
% 0.89/1.09      inference('sup-', [status(thm)], ['165', '179'])).
% 0.89/1.09  thf('181', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.09  thf('182', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.09  thf('183', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.89/1.09           = (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))))),
% 0.89/1.09      inference('demod', [status(thm)], ['73', '74'])).
% 0.89/1.09  thf('184', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (r1_tarski @ 
% 0.89/1.09          (k2_relat_1 @ 
% 0.89/1.09           (k4_relat_1 @ 
% 0.89/1.09            (k8_relat_1 @ X0 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X2))))) @ 
% 0.89/1.09          X2)),
% 0.89/1.09      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 0.89/1.09  thf('185', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (r1_tarski @ 
% 0.89/1.09          (k2_relat_1 @ 
% 0.89/1.09           (k4_relat_1 @ 
% 0.89/1.09            (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))) @ 
% 0.89/1.09          X1)),
% 0.89/1.09      inference('sup+', [status(thm)], ['164', '184'])).
% 0.89/1.09  thf('186', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf('187', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (r1_tarski @ 
% 0.89/1.09          (k2_relat_1 @ 
% 0.89/1.09           (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X2))) @ 
% 0.89/1.09          X1)),
% 0.89/1.09      inference('demod', [status(thm)], ['185', '186'])).
% 0.89/1.09  thf('188', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (r1_tarski @ 
% 0.89/1.09          (k2_relat_1 @ 
% 0.89/1.09           (k6_relat_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))) @ 
% 0.89/1.09          X2)),
% 0.89/1.09      inference('sup+', [status(thm)], ['163', '187'])).
% 0.89/1.09  thf('189', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 0.89/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.09  thf('190', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 0.89/1.09      inference('demod', [status(thm)], ['188', '189'])).
% 0.89/1.09  thf('191', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.89/1.09      inference('sup+', [status(thm)], ['162', '190'])).
% 0.89/1.09  thf('192', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.09          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.89/1.09              = (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['137', '138'])).
% 0.89/1.09  thf('193', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.89/1.09           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['11', '17', '18', '19', '20'])).
% 0.89/1.09  thf('194', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.09          | ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.09              = (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['192', '193'])).
% 0.89/1.09  thf('195', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.89/1.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf('196', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (r1_tarski @ X0 @ X1)
% 0.89/1.09          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['194', '195'])).
% 0.89/1.09  thf('197', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['191', '196'])).
% 0.89/1.09  thf('198', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['161', '197'])).
% 0.89/1.09  thf('199', plain,
% 0.89/1.09      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.89/1.09         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.89/1.09      inference('demod', [status(thm)], ['4', '198'])).
% 0.89/1.09  thf('200', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['133', '152'])).
% 0.89/1.09  thf('201', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['161', '197'])).
% 0.89/1.09  thf('202', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['200', '201'])).
% 0.89/1.09  thf('203', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.89/1.09           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['161', '197'])).
% 0.89/1.09  thf('204', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.89/1.09           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['202', '203'])).
% 0.89/1.09  thf('205', plain,
% 0.89/1.09      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.89/1.09         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.89/1.09      inference('demod', [status(thm)], ['199', '204'])).
% 0.89/1.09  thf('206', plain, ($false), inference('simplify', [status(thm)], ['205'])).
% 0.89/1.09  
% 0.89/1.09  % SZS output end Refutation
% 0.89/1.09  
% 0.89/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
