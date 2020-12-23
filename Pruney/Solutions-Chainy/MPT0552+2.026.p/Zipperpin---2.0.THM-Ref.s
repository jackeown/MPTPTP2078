%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R7fNaFgzvy

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:26 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 103 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  678 ( 959 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X4 @ X3 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('44',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R7fNaFgzvy
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 496 iterations in 0.423s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.68/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.68/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.68/0.89  thf(dt_k7_relat_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.68/0.89  thf(t148_relat_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ B ) =>
% 0.68/0.89       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.68/0.89          | ~ (v1_relat_1 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.89  thf(t100_relat_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ C ) =>
% 0.68/0.89       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.68/0.89         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.89         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.68/0.89            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.68/0.89          | ~ (v1_relat_1 @ X11))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.68/0.89  thf(commutativity_k2_tarski, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (![X3 : $i, X4 : $i]: ((k2_tarski @ X4 @ X3) = (k2_tarski @ X3 @ X4))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.68/0.89  thf(t12_setfam_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (![X7 : $i, X8 : $i]:
% 0.68/0.89         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.68/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X7 : $i, X8 : $i]:
% 0.68/0.89         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.68/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['5', '6'])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.89         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.68/0.89            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.68/0.89          | ~ (v1_relat_1 @ X11))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 0.68/0.89            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.68/0.89          | ~ (v1_relat_1 @ X2))),
% 0.68/0.89      inference('sup+', [status(thm)], ['7', '8'])).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 0.68/0.89            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ X2)
% 0.68/0.89          | ~ (v1_relat_1 @ X2))),
% 0.68/0.89      inference('sup+', [status(thm)], ['2', '9'])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X2)
% 0.68/0.89          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 0.68/0.89              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['10'])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.68/0.89          | ~ (v1_relat_1 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.89  thf(t88_relat_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (![X18 : $i, X19 : $i]:
% 0.68/0.89         ((r1_tarski @ (k7_relat_1 @ X18 @ X19) @ X18) | ~ (v1_relat_1 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.68/0.89  thf(t25_relat_1, axiom,
% 0.68/0.89    (![A:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ A ) =>
% 0.68/0.89       ( ![B:$i]:
% 0.68/0.89         ( ( v1_relat_1 @ B ) =>
% 0.68/0.89           ( ( r1_tarski @ A @ B ) =>
% 0.68/0.89             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.68/0.89               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      (![X16 : $i, X17 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X16)
% 0.68/0.89          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.68/0.89          | ~ (r1_tarski @ X17 @ X16)
% 0.68/0.89          | ~ (v1_relat_1 @ X17))),
% 0.68/0.89      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X0)
% 0.68/0.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.68/0.89          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.89             (k2_relat_1 @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.89           (k2_relat_1 @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.68/0.89          | ~ (v1_relat_1 @ X0))),
% 0.68/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X0)
% 0.68/0.89          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.89             (k2_relat_1 @ X0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['16', '17'])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ 
% 0.68/0.89           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.68/0.89           (k9_relat_1 @ X1 @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ X1)
% 0.68/0.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['12', '18'])).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X1)
% 0.68/0.89          | (r1_tarski @ 
% 0.68/0.89             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.68/0.89             (k9_relat_1 @ X1 @ X0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['19', '20'])).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ 
% 0.68/0.89           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 0.68/0.89           (k9_relat_1 @ X2 @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ X2)
% 0.68/0.89          | ~ (v1_relat_1 @ X2))),
% 0.68/0.89      inference('sup+', [status(thm)], ['11', '21'])).
% 0.68/0.89  thf('23', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X2)
% 0.68/0.89          | (r1_tarski @ 
% 0.68/0.89             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 0.68/0.89             (k9_relat_1 @ X2 @ X0)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['22'])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 0.68/0.89           (k9_relat_1 @ X2 @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 0.68/0.89          | ~ (v1_relat_1 @ X2))),
% 0.68/0.89      inference('sup+', [status(thm)], ['1', '23'])).
% 0.68/0.89  thf('25', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X2)
% 0.68/0.89          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 0.68/0.89             (k9_relat_1 @ X2 @ X0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.68/0.89          | ~ (v1_relat_1 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.89  thf('28', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.68/0.89          | ~ (v1_relat_1 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.89  thf('29', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X0)
% 0.68/0.89          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.68/0.89             (k2_relat_1 @ X0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['16', '17'])).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.68/0.89          | ~ (v1_relat_1 @ X1)
% 0.68/0.89          | ~ (v1_relat_1 @ X1))),
% 0.68/0.89      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X1)
% 0.68/0.89          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['30'])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.68/0.89           (k9_relat_1 @ X1 @ X0))
% 0.68/0.89          | ~ (v1_relat_1 @ X1)
% 0.68/0.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.68/0.89      inference('sup+', [status(thm)], ['27', '31'])).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X9 : $i, X10 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X9) | (v1_relat_1 @ (k7_relat_1 @ X9 @ X10)))),
% 0.68/0.89      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X1)
% 0.68/0.89          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.68/0.89             (k9_relat_1 @ X1 @ X0)))),
% 0.68/0.89      inference('clc', [status(thm)], ['32', '33'])).
% 0.68/0.89  thf(t19_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.68/0.89       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X0 @ X1)
% 0.68/0.89          | ~ (r1_tarski @ X0 @ X2)
% 0.68/0.89          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.68/0.89  thf('36', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X1)
% 0.68/0.89          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.68/0.89             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 0.68/0.89          | ~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X3))),
% 0.68/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.89  thf('37', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X1)
% 0.68/0.89          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 0.68/0.89             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.68/0.89          | ~ (v1_relat_1 @ X1))),
% 0.68/0.89      inference('sup-', [status(thm)], ['26', '36'])).
% 0.68/0.89  thf('38', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 0.68/0.89           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.68/0.89          | ~ (v1_relat_1 @ X1))),
% 0.68/0.89      inference('simplify', [status(thm)], ['37'])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.68/0.89          | ~ (v1_relat_1 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.89  thf('40', plain,
% 0.68/0.89      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.89         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 0.68/0.89            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 0.68/0.89          | ~ (v1_relat_1 @ X11))),
% 0.68/0.89      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.68/0.89          | ~ (v1_relat_1 @ X14))),
% 0.68/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.68/0.89  thf('42', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.68/0.89            = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.68/0.89          | ~ (v1_relat_1 @ X2)
% 0.68/0.89          | ~ (v1_relat_1 @ X2))),
% 0.68/0.89      inference('sup+', [status(thm)], ['40', '41'])).
% 0.68/0.89  thf('43', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         (~ (v1_relat_1 @ X2)
% 0.68/0.89          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.68/0.89              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.68/0.89      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.89  thf(t154_relat_1, conjecture,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( v1_relat_1 @ C ) =>
% 0.68/0.89       ( r1_tarski @
% 0.68/0.89         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.68/0.89         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.89        ( ( v1_relat_1 @ C ) =>
% 0.68/0.89          ( r1_tarski @
% 0.68/0.89            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.68/0.89            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.68/0.89          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.68/0.89           (k9_relat_1 @ sk_C @ sk_B)))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      ((~ (r1_tarski @ 
% 0.68/0.89           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)) @ 
% 0.68/0.89           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.68/0.89            (k9_relat_1 @ sk_C @ sk_B)))
% 0.68/0.89        | ~ (v1_relat_1 @ sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.89  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (~ (r1_tarski @ 
% 0.68/0.89          (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)) @ 
% 0.68/0.89          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.68/0.89           (k9_relat_1 @ sk_C @ sk_B)))),
% 0.68/0.89      inference('demod', [status(thm)], ['45', '46'])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      ((~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.68/0.89           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.68/0.89            (k9_relat_1 @ sk_C @ sk_B)))
% 0.68/0.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['39', '47'])).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['38', '48'])).
% 0.68/0.89  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('51', plain, (~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))),
% 0.68/0.89      inference('demod', [status(thm)], ['49', '50'])).
% 0.68/0.89  thf('52', plain, (~ (v1_relat_1 @ sk_C)),
% 0.68/0.89      inference('sup-', [status(thm)], ['0', '51'])).
% 0.68/0.89  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.76/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
