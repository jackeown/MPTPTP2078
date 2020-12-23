%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wTG6iY5NPQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:28 EST 2020

% Result     : Theorem 7.41s
% Output     : Refutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 153 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  991 (1543 expanded)
%              Number of equality atoms :   28 (  66 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t106_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ ( k7_relat_1 @ X16 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t106_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X3 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X3 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('64',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ sk_B ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ sk_B ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wTG6iY5NPQ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.41/7.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.41/7.65  % Solved by: fo/fo7.sh
% 7.41/7.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.41/7.65  % done 3022 iterations in 7.224s
% 7.41/7.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.41/7.65  % SZS output start Refutation
% 7.41/7.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.41/7.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.41/7.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.41/7.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 7.41/7.65  thf(sk_A_type, type, sk_A: $i).
% 7.41/7.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.41/7.65  thf(sk_B_type, type, sk_B: $i).
% 7.41/7.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.41/7.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 7.41/7.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.41/7.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.41/7.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.41/7.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.41/7.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.41/7.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.41/7.65  thf(t148_relat_1, axiom,
% 7.41/7.65    (![A:$i,B:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ B ) =>
% 7.41/7.65       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 7.41/7.65  thf('0', plain,
% 7.41/7.65      (![X20 : $i, X21 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 7.41/7.65          | ~ (v1_relat_1 @ X20))),
% 7.41/7.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.41/7.65  thf(t70_enumset1, axiom,
% 7.41/7.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.41/7.65  thf('1', plain,
% 7.41/7.65      (![X7 : $i, X8 : $i]:
% 7.41/7.65         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 7.41/7.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.41/7.65  thf(t100_relat_1, axiom,
% 7.41/7.65    (![A:$i,B:$i,C:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ C ) =>
% 7.41/7.65       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 7.41/7.65         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 7.41/7.65  thf('2', plain,
% 7.41/7.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.41/7.65         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 7.41/7.65            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15)))
% 7.41/7.65          | ~ (v1_relat_1 @ X13))),
% 7.41/7.65      inference('cnf', [status(esa)], [t100_relat_1])).
% 7.41/7.65  thf(t12_setfam_1, axiom,
% 7.41/7.65    (![A:$i,B:$i]:
% 7.41/7.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.41/7.65  thf('3', plain,
% 7.41/7.65      (![X9 : $i, X10 : $i]:
% 7.41/7.65         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 7.41/7.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.41/7.65  thf('4', plain,
% 7.41/7.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.41/7.65         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 7.41/7.65            = (k7_relat_1 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X14 @ X15))))
% 7.41/7.65          | ~ (v1_relat_1 @ X13))),
% 7.41/7.65      inference('demod', [status(thm)], ['2', '3'])).
% 7.41/7.65  thf('5', plain,
% 7.41/7.65      (![X20 : $i, X21 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 7.41/7.65          | ~ (v1_relat_1 @ X20))),
% 7.41/7.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.41/7.65  thf('6', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65            = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 7.41/7.65          | ~ (v1_relat_1 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['4', '5'])).
% 7.41/7.65  thf('7', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65              = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 7.41/7.65      inference('simplify', [status(thm)], ['6'])).
% 7.41/7.65  thf('8', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65            = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['1', '7'])).
% 7.41/7.65  thf('9', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65            = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['1', '7'])).
% 7.41/7.65  thf('10', plain,
% 7.41/7.65      (![X20 : $i, X21 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 7.41/7.65          | ~ (v1_relat_1 @ X20))),
% 7.41/7.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.41/7.65  thf('11', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 7.41/7.65            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 7.41/7.65      inference('sup+', [status(thm)], ['9', '10'])).
% 7.41/7.65  thf(dt_k7_relat_1, axiom,
% 7.41/7.65    (![A:$i,B:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 7.41/7.65  thf('12', plain,
% 7.41/7.65      (![X11 : $i, X12 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 7.41/7.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.41/7.65  thf('13', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | ((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 7.41/7.65              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 7.41/7.65      inference('clc', [status(thm)], ['11', '12'])).
% 7.41/7.65  thf('14', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['8', '13'])).
% 7.41/7.65  thf('15', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 7.41/7.65      inference('simplify', [status(thm)], ['14'])).
% 7.41/7.65  thf('16', plain,
% 7.41/7.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.41/7.65         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 7.41/7.65            = (k7_relat_1 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X14 @ X15))))
% 7.41/7.65          | ~ (v1_relat_1 @ X13))),
% 7.41/7.65      inference('demod', [status(thm)], ['2', '3'])).
% 7.41/7.65  thf('17', plain,
% 7.41/7.65      (![X11 : $i, X12 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 7.41/7.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.41/7.65  thf('18', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['16', '17'])).
% 7.41/7.65  thf('19', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 7.41/7.65      inference('simplify', [status(thm)], ['18'])).
% 7.41/7.65  thf(d3_tarski, axiom,
% 7.41/7.65    (![A:$i,B:$i]:
% 7.41/7.65     ( ( r1_tarski @ A @ B ) <=>
% 7.41/7.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.41/7.65  thf('20', plain,
% 7.41/7.65      (![X1 : $i, X3 : $i]:
% 7.41/7.65         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.41/7.65      inference('cnf', [status(esa)], [d3_tarski])).
% 7.41/7.65  thf('21', plain,
% 7.41/7.65      (![X1 : $i, X3 : $i]:
% 7.41/7.65         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.41/7.65      inference('cnf', [status(esa)], [d3_tarski])).
% 7.41/7.65  thf('22', plain,
% 7.41/7.65      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 7.41/7.65      inference('sup-', [status(thm)], ['20', '21'])).
% 7.41/7.65  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 7.41/7.65      inference('simplify', [status(thm)], ['22'])).
% 7.41/7.65  thf('24', plain,
% 7.41/7.65      (![X11 : $i, X12 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 7.41/7.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.41/7.65  thf(t88_relat_1, axiom,
% 7.41/7.65    (![A:$i,B:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 7.41/7.65  thf('25', plain,
% 7.41/7.65      (![X24 : $i, X25 : $i]:
% 7.41/7.65         ((r1_tarski @ (k7_relat_1 @ X24 @ X25) @ X24) | ~ (v1_relat_1 @ X24))),
% 7.41/7.65      inference('cnf', [status(esa)], [t88_relat_1])).
% 7.41/7.65  thf(t106_relat_1, axiom,
% 7.41/7.65    (![A:$i,B:$i,C:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ C ) =>
% 7.41/7.65       ( ![D:$i]:
% 7.41/7.65         ( ( v1_relat_1 @ D ) =>
% 7.41/7.65           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 7.41/7.65             ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ))).
% 7.41/7.65  thf('26', plain,
% 7.41/7.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X16)
% 7.41/7.65          | (r1_tarski @ (k7_relat_1 @ X17 @ X18) @ (k7_relat_1 @ X16 @ X19))
% 7.41/7.65          | ~ (r1_tarski @ X17 @ X16)
% 7.41/7.65          | ~ (r1_tarski @ X18 @ X19)
% 7.41/7.65          | ~ (v1_relat_1 @ X17))),
% 7.41/7.65      inference('cnf', [status(esa)], [t106_relat_1])).
% 7.41/7.65  thf('27', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X0)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.41/7.65          | ~ (r1_tarski @ X3 @ X2)
% 7.41/7.65          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X3) @ 
% 7.41/7.65             (k7_relat_1 @ X0 @ X2))
% 7.41/7.65          | ~ (v1_relat_1 @ X0))),
% 7.41/7.65      inference('sup-', [status(thm)], ['25', '26'])).
% 7.41/7.65  thf('28', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.41/7.65         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X3) @ 
% 7.41/7.65           (k7_relat_1 @ X0 @ X2))
% 7.41/7.65          | ~ (r1_tarski @ X3 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.41/7.65          | ~ (v1_relat_1 @ X0))),
% 7.41/7.65      inference('simplify', [status(thm)], ['27'])).
% 7.41/7.65  thf('29', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | ~ (v1_relat_1 @ X1)
% 7.41/7.65          | ~ (r1_tarski @ X3 @ X2)
% 7.41/7.65          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X3) @ 
% 7.41/7.65             (k7_relat_1 @ X1 @ X2)))),
% 7.41/7.65      inference('sup-', [status(thm)], ['24', '28'])).
% 7.41/7.65  thf('30', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.41/7.65         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X3) @ 
% 7.41/7.65           (k7_relat_1 @ X1 @ X2))
% 7.41/7.65          | ~ (r1_tarski @ X3 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ X1))),
% 7.41/7.65      inference('simplify', [status(thm)], ['29'])).
% 7.41/7.65  thf('31', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 7.41/7.65             (k7_relat_1 @ X1 @ X0)))),
% 7.41/7.65      inference('sup-', [status(thm)], ['23', '30'])).
% 7.41/7.65  thf(t25_relat_1, axiom,
% 7.41/7.65    (![A:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ A ) =>
% 7.41/7.65       ( ![B:$i]:
% 7.41/7.65         ( ( v1_relat_1 @ B ) =>
% 7.41/7.65           ( ( r1_tarski @ A @ B ) =>
% 7.41/7.65             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 7.41/7.65               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 7.41/7.65  thf('32', plain,
% 7.41/7.65      (![X22 : $i, X23 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X22)
% 7.41/7.65          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 7.41/7.65          | ~ (r1_tarski @ X23 @ X22)
% 7.41/7.65          | ~ (v1_relat_1 @ X23))),
% 7.41/7.65      inference('cnf', [status(esa)], [t25_relat_1])).
% 7.41/7.65  thf('33', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 7.41/7.65          | (r1_tarski @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.41/7.65      inference('sup-', [status(thm)], ['31', '32'])).
% 7.41/7.65  thf('34', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0))
% 7.41/7.65          | (r1_tarski @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup-', [status(thm)], ['19', '33'])).
% 7.41/7.65  thf('35', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         ((r1_tarski @ 
% 7.41/7.65           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 7.41/7.65           (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('simplify', [status(thm)], ['34'])).
% 7.41/7.65  thf('36', plain,
% 7.41/7.65      (![X11 : $i, X12 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 7.41/7.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.41/7.65  thf('37', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | (r1_tarski @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ X2 @ X0))))),
% 7.41/7.65      inference('clc', [status(thm)], ['35', '36'])).
% 7.41/7.65  thf('38', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 7.41/7.65           (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 7.41/7.65          | ~ (v1_relat_1 @ X2)
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['15', '37'])).
% 7.41/7.65  thf('39', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 7.41/7.65             (k2_relat_1 @ (k7_relat_1 @ X2 @ X0))))),
% 7.41/7.65      inference('simplify', [status(thm)], ['38'])).
% 7.41/7.65  thf('40', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 7.41/7.65           (k9_relat_1 @ X1 @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X1)
% 7.41/7.65          | ~ (v1_relat_1 @ X1))),
% 7.41/7.65      inference('sup+', [status(thm)], ['0', '39'])).
% 7.41/7.65  thf('41', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 7.41/7.65             (k9_relat_1 @ X1 @ X0)))),
% 7.41/7.65      inference('simplify', [status(thm)], ['40'])).
% 7.41/7.65  thf('42', plain,
% 7.41/7.65      (![X20 : $i, X21 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 7.41/7.65          | ~ (v1_relat_1 @ X20))),
% 7.41/7.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.41/7.65  thf('43', plain,
% 7.41/7.65      (![X20 : $i, X21 : $i]:
% 7.41/7.65         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 7.41/7.65          | ~ (v1_relat_1 @ X20))),
% 7.41/7.65      inference('cnf', [status(esa)], [t148_relat_1])).
% 7.41/7.65  thf('44', plain,
% 7.41/7.65      (![X24 : $i, X25 : $i]:
% 7.41/7.65         ((r1_tarski @ (k7_relat_1 @ X24 @ X25) @ X24) | ~ (v1_relat_1 @ X24))),
% 7.41/7.65      inference('cnf', [status(esa)], [t88_relat_1])).
% 7.41/7.65  thf('45', plain,
% 7.41/7.65      (![X22 : $i, X23 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X22)
% 7.41/7.65          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 7.41/7.65          | ~ (r1_tarski @ X23 @ X22)
% 7.41/7.65          | ~ (v1_relat_1 @ X23))),
% 7.41/7.65      inference('cnf', [status(esa)], [t25_relat_1])).
% 7.41/7.65  thf('46', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X0)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.41/7.65          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 7.41/7.65             (k2_relat_1 @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X0))),
% 7.41/7.65      inference('sup-', [status(thm)], ['44', '45'])).
% 7.41/7.65  thf('47', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i]:
% 7.41/7.65         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 7.41/7.65           (k2_relat_1 @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.41/7.65          | ~ (v1_relat_1 @ X0))),
% 7.41/7.65      inference('simplify', [status(thm)], ['46'])).
% 7.41/7.65  thf('48', plain,
% 7.41/7.65      (![X11 : $i, X12 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 7.41/7.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.41/7.65  thf('49', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X0)
% 7.41/7.65          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 7.41/7.65             (k2_relat_1 @ X0)))),
% 7.41/7.65      inference('clc', [status(thm)], ['47', '48'])).
% 7.41/7.65  thf('50', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i]:
% 7.41/7.65         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 7.41/7.65          | ~ (v1_relat_1 @ X1)
% 7.41/7.65          | ~ (v1_relat_1 @ X1))),
% 7.41/7.65      inference('sup+', [status(thm)], ['43', '49'])).
% 7.41/7.65  thf('51', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 7.41/7.65      inference('simplify', [status(thm)], ['50'])).
% 7.41/7.65  thf('52', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 7.41/7.65           (k9_relat_1 @ X1 @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X1)
% 7.41/7.65          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 7.41/7.65      inference('sup+', [status(thm)], ['42', '51'])).
% 7.41/7.65  thf('53', plain,
% 7.41/7.65      (![X11 : $i, X12 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 7.41/7.65      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.41/7.65  thf('54', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 7.41/7.65             (k9_relat_1 @ X1 @ X0)))),
% 7.41/7.65      inference('clc', [status(thm)], ['52', '53'])).
% 7.41/7.65  thf(t19_xboole_1, axiom,
% 7.41/7.65    (![A:$i,B:$i,C:$i]:
% 7.41/7.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 7.41/7.65       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.41/7.65  thf('55', plain,
% 7.41/7.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 7.41/7.65         (~ (r1_tarski @ X4 @ X5)
% 7.41/7.65          | ~ (r1_tarski @ X4 @ X6)
% 7.41/7.65          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.41/7.65      inference('cnf', [status(esa)], [t19_xboole_1])).
% 7.41/7.65  thf('56', plain,
% 7.41/7.65      (![X9 : $i, X10 : $i]:
% 7.41/7.65         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 7.41/7.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.41/7.65  thf('57', plain,
% 7.41/7.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 7.41/7.65         (~ (r1_tarski @ X4 @ X5)
% 7.41/7.65          | ~ (r1_tarski @ X4 @ X6)
% 7.41/7.65          | (r1_tarski @ X4 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 7.41/7.65      inference('demod', [status(thm)], ['55', '56'])).
% 7.41/7.65  thf('58', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 7.41/7.65             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X3)))
% 7.41/7.65          | ~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X3))),
% 7.41/7.65      inference('sup-', [status(thm)], ['54', '57'])).
% 7.41/7.65  thf('59', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X1)
% 7.41/7.65          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 7.41/7.65             (k1_setfam_1 @ 
% 7.41/7.65              (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 7.41/7.65          | ~ (v1_relat_1 @ X1))),
% 7.41/7.65      inference('sup-', [status(thm)], ['41', '58'])).
% 7.41/7.65  thf('60', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 7.41/7.65           (k1_setfam_1 @ 
% 7.41/7.65            (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 7.41/7.65          | ~ (v1_relat_1 @ X1))),
% 7.41/7.65      inference('simplify', [status(thm)], ['59'])).
% 7.41/7.65  thf('61', plain,
% 7.41/7.65      (![X7 : $i, X8 : $i]:
% 7.41/7.65         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 7.41/7.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.41/7.65  thf('62', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (~ (v1_relat_1 @ X2)
% 7.41/7.65          | ((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 7.41/7.65              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 7.41/7.65      inference('clc', [status(thm)], ['11', '12'])).
% 7.41/7.65  thf('63', plain,
% 7.41/7.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.41/7.65         (((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 7.41/7.65            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 7.41/7.65          | ~ (v1_relat_1 @ X2))),
% 7.41/7.65      inference('sup+', [status(thm)], ['61', '62'])).
% 7.41/7.65  thf(t154_relat_1, conjecture,
% 7.41/7.65    (![A:$i,B:$i,C:$i]:
% 7.41/7.65     ( ( v1_relat_1 @ C ) =>
% 7.41/7.65       ( r1_tarski @
% 7.41/7.65         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.41/7.65         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 7.41/7.65  thf(zf_stmt_0, negated_conjecture,
% 7.41/7.65    (~( ![A:$i,B:$i,C:$i]:
% 7.41/7.65        ( ( v1_relat_1 @ C ) =>
% 7.41/7.65          ( r1_tarski @
% 7.41/7.65            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.41/7.65            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 7.41/7.65    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 7.41/7.65  thf('64', plain,
% 7.41/7.65      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 7.41/7.65          (k3_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 7.41/7.65           (k9_relat_1 @ sk_C_1 @ sk_B)))),
% 7.41/7.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.41/7.65  thf('65', plain,
% 7.41/7.65      (![X9 : $i, X10 : $i]:
% 7.41/7.65         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 7.41/7.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.41/7.65  thf('66', plain,
% 7.41/7.65      (![X9 : $i, X10 : $i]:
% 7.41/7.65         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 7.41/7.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.41/7.65  thf('67', plain,
% 7.41/7.65      (~ (r1_tarski @ 
% 7.41/7.65          (k9_relat_1 @ sk_C_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 7.41/7.65          (k1_setfam_1 @ 
% 7.41/7.65           (k2_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 7.41/7.65            (k9_relat_1 @ sk_C_1 @ sk_B))))),
% 7.41/7.65      inference('demod', [status(thm)], ['64', '65', '66'])).
% 7.41/7.65  thf('68', plain,
% 7.41/7.65      ((~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A) @ sk_B) @ 
% 7.41/7.65           (k1_setfam_1 @ 
% 7.41/7.65            (k2_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 7.41/7.65             (k9_relat_1 @ sk_C_1 @ sk_B))))
% 7.41/7.65        | ~ (v1_relat_1 @ sk_C_1))),
% 7.41/7.65      inference('sup-', [status(thm)], ['63', '67'])).
% 7.41/7.65  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 7.41/7.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.41/7.65  thf('70', plain,
% 7.41/7.65      (~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A) @ sk_B) @ 
% 7.41/7.65          (k1_setfam_1 @ 
% 7.41/7.65           (k2_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 7.41/7.65            (k9_relat_1 @ sk_C_1 @ sk_B))))),
% 7.41/7.65      inference('demod', [status(thm)], ['68', '69'])).
% 7.41/7.65  thf('71', plain, (~ (v1_relat_1 @ sk_C_1)),
% 7.41/7.65      inference('sup-', [status(thm)], ['60', '70'])).
% 7.41/7.65  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 7.41/7.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.41/7.65  thf('73', plain, ($false), inference('demod', [status(thm)], ['71', '72'])).
% 7.41/7.65  
% 7.41/7.65  % SZS output end Refutation
% 7.41/7.65  
% 7.41/7.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
