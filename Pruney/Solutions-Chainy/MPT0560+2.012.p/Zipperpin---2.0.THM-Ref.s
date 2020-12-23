%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FvRcWPonqi

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 151 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   19
%              Number of atoms          :  674 (1129 expanded)
%              Number of equality atoms :   52 (  87 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ ( k1_relat_1 @ X31 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k8_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ X11 @ ( k6_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','11'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('21',plain,
    ( ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k8_relat_1 @ X13 @ ( k7_relat_1 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X9 @ X10 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k7_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('30',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ X0 ) ) @ ( k8_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k8_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k8_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_B ) )
    | ( ( k8_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X28 @ X27 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k8_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k9_relat_1 @ X18 @ ( k9_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FvRcWPonqi
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 297 iterations in 0.203s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.45/0.66  thf(t94_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.45/0.66          | ~ (v1_relat_1 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.66  thf(t71_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.45/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.66  thf('1', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf(t98_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X31 @ (k1_relat_1 @ X31)) = (X31))
% 0.45/0.66          | ~ (v1_relat_1 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.66  thf('4', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.66  thf(t123_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         (((k8_relat_1 @ X12 @ X11) = (k5_relat_1 @ X11 @ (k6_relat_1 @ X12)))
% 0.45/0.66          | ~ (v1_relat_1 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.45/0.66          | ~ (v1_relat_1 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('10', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['5', '11'])).
% 0.45/0.66  thf(t162_relat_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ![B:$i,C:$i]:
% 0.45/0.66         ( ( r1_tarski @ B @ C ) =>
% 0.45/0.66           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.45/0.66             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( v1_relat_1 @ A ) =>
% 0.45/0.66          ( ![B:$i,C:$i]:
% 0.45/0.66            ( ( r1_tarski @ B @ C ) =>
% 0.45/0.66              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.45/0.66                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 0.45/0.66  thf('13', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('14', plain, (![X21 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf(t97_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.45/0.66         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.45/0.66          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 0.45/0.66          | ~ (v1_relat_1 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.45/0.66          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.66  thf('17', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.66          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (((k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_C)) = (k6_relat_1 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf(t140_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ C ) =>
% 0.45/0.66       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.45/0.66         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.66         (((k7_relat_1 @ (k8_relat_1 @ X13 @ X14) @ X15)
% 0.45/0.66            = (k8_relat_1 @ X13 @ (k7_relat_1 @ X14 @ X15)))
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.45/0.66  thf(t117_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X9 : $i, X10 : $i]:
% 0.45/0.66         ((r1_tarski @ (k8_relat_1 @ X9 @ X10) @ X10) | ~ (v1_relat_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((r1_tarski @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0) @ 
% 0.45/0.66           (k7_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf(dt_k7_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X1)
% 0.45/0.66          | (r1_tarski @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0) @ 
% 0.45/0.66             (k7_relat_1 @ X1 @ X0)))),
% 0.45/0.66      inference('clc', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 0.45/0.66           (k7_relat_1 @ (k6_relat_1 @ sk_C) @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['21', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.66  thf('30', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (r1_tarski @ (k8_relat_1 @ sk_B @ (k6_relat_1 @ X0)) @ 
% 0.45/0.66          (k8_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((r1_tarski @ (k6_relat_1 @ sk_B) @ 
% 0.45/0.66        (k8_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['12', '31'])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i]:
% 0.45/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k8_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ 
% 0.45/0.66           (k6_relat_1 @ sk_B))
% 0.45/0.66        | ((k8_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (k6_relat_1 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X27 : $i, X28 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X28 @ X27) = (k5_relat_1 @ (k6_relat_1 @ X27) @ X28))
% 0.45/0.66          | ~ (v1_relat_1 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.45/0.66  thf(t76_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.45/0.66         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X23 : $i, X24 : $i]:
% 0.45/0.66         ((r1_tarski @ (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)) @ X23)
% 0.45/0.66          | ~ (v1_relat_1 @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.45/0.66           (k6_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('39', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (((k8_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (k6_relat_1 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['34', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.45/0.66           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.66  thf(t148_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.45/0.66          | ~ (v1_relat_1 @ X16))),
% 0.45/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.45/0.66            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.45/0.66           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 0.45/0.66         = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['43', '48'])).
% 0.45/0.66  thf('50', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.45/0.66  thf('51', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.45/0.66  thf(t159_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( v1_relat_1 @ C ) =>
% 0.45/0.66           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.45/0.66             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X18)
% 0.45/0.66          | ((k9_relat_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 0.45/0.66              = (k9_relat_1 @ X18 @ (k9_relat_1 @ X19 @ X20)))
% 0.45/0.66          | ~ (v1_relat_1 @ X19))),
% 0.45/0.66      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 0.45/0.66            = (k9_relat_1 @ X0 @ sk_B))
% 0.45/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['51', '52'])).
% 0.45/0.66  thf('54', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 0.45/0.66            = (k9_relat_1 @ X0 @ sk_B))
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 0.45/0.66            = (k9_relat_1 @ X0 @ sk_B))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['0', '55'])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 0.45/0.66              = (k9_relat_1 @ X0 @ sk_B)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.45/0.66         != (k9_relat_1 @ sk_A @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.66  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.66  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
