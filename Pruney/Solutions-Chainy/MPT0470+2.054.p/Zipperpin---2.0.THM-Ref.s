%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mDKdzNql2d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:34 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 455 expanded)
%              Number of leaves         :   27 ( 153 expanded)
%              Depth                    :   29
%              Number of atoms          :  895 (3093 expanded)
%              Number of equality atoms :   60 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X23 @ X22 ) ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('20',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('21',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','16','53'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','52'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('77',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ X2 @ X1 ) ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,
    ( ! [X1: $i,X2: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ X2 @ X1 ) ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ! [X1: $i,X2: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ X2 @ X1 ) ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('89',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('90',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('101',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['86','101'])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['103','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mDKdzNql2d
% 0.17/0.38  % Computer   : n020.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 15:23:37 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 1.13/1.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.36  % Solved by: fo/fo7.sh
% 1.13/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.36  % done 1734 iterations in 0.865s
% 1.13/1.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.36  % SZS output start Refutation
% 1.13/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.36  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.13/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.13/1.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.13/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.36  thf(sk_B_type, type, sk_B: $i > $i).
% 1.13/1.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.36  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.13/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.13/1.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.36  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.13/1.36  thf(dt_k5_relat_1, axiom,
% 1.13/1.36    (![A:$i,B:$i]:
% 1.13/1.36     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.13/1.36       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.13/1.36  thf('0', plain,
% 1.13/1.36      (![X16 : $i, X17 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X16)
% 1.13/1.36          | ~ (v1_relat_1 @ X17)
% 1.13/1.36          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.13/1.36  thf(t60_relat_1, axiom,
% 1.13/1.36    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.13/1.36     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.13/1.36  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.13/1.36      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.13/1.36  thf(t45_relat_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( v1_relat_1 @ A ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( v1_relat_1 @ B ) =>
% 1.13/1.36           ( r1_tarski @
% 1.13/1.36             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.13/1.36  thf('2', plain,
% 1.13/1.36      (![X22 : $i, X23 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X22)
% 1.13/1.36          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X23 @ X22)) @ 
% 1.13/1.36             (k2_relat_1 @ X22))
% 1.13/1.36          | ~ (v1_relat_1 @ X23))),
% 1.13/1.36      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.13/1.36  thf(t28_xboole_1, axiom,
% 1.13/1.36    (![A:$i,B:$i]:
% 1.13/1.36     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.13/1.36  thf('3', plain,
% 1.13/1.36      (![X13 : $i, X14 : $i]:
% 1.13/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.13/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.13/1.36  thf('4', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X1)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.13/1.36              (k2_relat_1 @ X0)) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['2', '3'])).
% 1.13/1.36  thf('5', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.13/1.36            k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.13/1.36          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('sup+', [status(thm)], ['1', '4'])).
% 1.13/1.36  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.13/1.36  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf(t3_xboole_0, axiom,
% 1.13/1.36    (![A:$i,B:$i]:
% 1.13/1.36     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.13/1.36            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.13/1.36       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.13/1.36            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.13/1.36  thf('7', plain,
% 1.13/1.36      (![X4 : $i, X5 : $i]:
% 1.13/1.36         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 1.13/1.36      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.13/1.36  thf(d1_xboole_0, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.13/1.36  thf('8', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.36      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.36  thf('9', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['7', '8'])).
% 1.13/1.36  thf('10', plain,
% 1.13/1.36      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.13/1.36      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.13/1.36  thf(t4_xboole_0, axiom,
% 1.13/1.36    (![A:$i,B:$i]:
% 1.13/1.36     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.13/1.36            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.13/1.36       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.13/1.36            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.13/1.36  thf('11', plain,
% 1.13/1.36      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.13/1.36         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.13/1.36          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.13/1.36      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.13/1.36  thf('12', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['10', '11'])).
% 1.13/1.36  thf('13', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['9', '12'])).
% 1.13/1.36  thf(l13_xboole_0, axiom,
% 1.13/1.36    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.13/1.36  thf('14', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('15', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.36  thf('16', plain,
% 1.13/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['6', '15'])).
% 1.13/1.36  thf(t62_relat_1, conjecture,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( v1_relat_1 @ A ) =>
% 1.13/1.36       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.13/1.36         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.13/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.36    (~( ![A:$i]:
% 1.13/1.36        ( ( v1_relat_1 @ A ) =>
% 1.13/1.36          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.13/1.36            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.13/1.36    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.13/1.36  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf(cc1_relat_1, axiom,
% 1.13/1.36    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.13/1.36  thf('18', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 1.13/1.36      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.13/1.36  thf('19', plain,
% 1.13/1.36      (![X16 : $i, X17 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X16)
% 1.13/1.36          | ~ (v1_relat_1 @ X17)
% 1.13/1.36          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.13/1.36  thf('20', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 1.13/1.36      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.13/1.36  thf('21', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.13/1.36      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.13/1.36  thf(t44_relat_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( v1_relat_1 @ A ) =>
% 1.13/1.36       ( ![B:$i]:
% 1.13/1.36         ( ( v1_relat_1 @ B ) =>
% 1.13/1.36           ( r1_tarski @
% 1.13/1.36             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.13/1.36  thf('22', plain,
% 1.13/1.36      (![X20 : $i, X21 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X20)
% 1.13/1.36          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X21 @ X20)) @ 
% 1.13/1.36             (k1_relat_1 @ X21))
% 1.13/1.36          | ~ (v1_relat_1 @ X21))),
% 1.13/1.36      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.13/1.36  thf('23', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.13/1.36           k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('sup+', [status(thm)], ['21', '22'])).
% 1.13/1.36  thf('24', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.13/1.36             k1_xboole_0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['20', '23'])).
% 1.13/1.36  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('26', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.13/1.36             k1_xboole_0))),
% 1.13/1.36      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.36  thf('27', plain,
% 1.13/1.36      (![X13 : $i, X14 : $i]:
% 1.13/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.13/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.13/1.36  thf('28', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.13/1.36              k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['26', '27'])).
% 1.13/1.36  thf('29', plain,
% 1.13/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['6', '15'])).
% 1.13/1.36  thf('30', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.13/1.36      inference('demod', [status(thm)], ['28', '29'])).
% 1.13/1.36  thf(fc8_relat_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.13/1.36       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.13/1.36  thf('31', plain,
% 1.13/1.36      (![X18 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ (k1_relat_1 @ X18))
% 1.13/1.36          | ~ (v1_relat_1 @ X18)
% 1.13/1.36          | (v1_xboole_0 @ X18))),
% 1.13/1.36      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.13/1.36  thf('32', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.13/1.36          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['30', '31'])).
% 1.13/1.36  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('34', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.13/1.36          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['32', '33'])).
% 1.13/1.36  thf('35', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['19', '34'])).
% 1.13/1.36  thf('36', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.13/1.36          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('simplify', [status(thm)], ['35'])).
% 1.13/1.36  thf('37', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['18', '36'])).
% 1.13/1.36  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('39', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['37', '38'])).
% 1.13/1.36  thf('40', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 1.13/1.36      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.13/1.36  thf('41', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('42', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['37', '38'])).
% 1.13/1.36  thf('43', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('44', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['42', '43'])).
% 1.13/1.36  thf('45', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.13/1.36          | ~ (v1_xboole_0 @ X0)
% 1.13/1.36          | ~ (v1_relat_1 @ X1))),
% 1.13/1.36      inference('sup+', [status(thm)], ['41', '44'])).
% 1.13/1.36  thf('46', plain,
% 1.13/1.36      (![X16 : $i, X17 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X16)
% 1.13/1.36          | ~ (v1_relat_1 @ X17)
% 1.13/1.36          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 1.13/1.36      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.13/1.36  thf('47', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         ((v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | ~ (v1_xboole_0 @ X1)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | ~ (v1_relat_1 @ X1))),
% 1.13/1.36      inference('sup+', [status(thm)], ['45', '46'])).
% 1.13/1.36  thf('48', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X1)
% 1.13/1.36          | ~ (v1_xboole_0 @ X1)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_relat_1 @ k1_xboole_0))),
% 1.13/1.36      inference('simplify', [status(thm)], ['47'])).
% 1.13/1.36  thf('49', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ X0)
% 1.13/1.36          | (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X1)
% 1.13/1.36          | ~ (v1_xboole_0 @ X0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['40', '48'])).
% 1.13/1.36  thf('50', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X1)
% 1.13/1.36          | (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_xboole_0 @ X0))),
% 1.13/1.36      inference('simplify', [status(thm)], ['49'])).
% 1.13/1.36  thf('51', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X1))),
% 1.13/1.36      inference('sup-', [status(thm)], ['39', '50'])).
% 1.13/1.36  thf('52', plain,
% 1.13/1.36      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.13/1.36      inference('condensation', [status(thm)], ['51'])).
% 1.13/1.36  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.13/1.36      inference('sup-', [status(thm)], ['17', '52'])).
% 1.13/1.36  thf('54', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['5', '16', '53'])).
% 1.13/1.36  thf(fc9_relat_1, axiom,
% 1.13/1.36    (![A:$i]:
% 1.13/1.36     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.13/1.36       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.13/1.36  thf('55', plain,
% 1.13/1.36      (![X19 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ (k2_relat_1 @ X19))
% 1.13/1.36          | ~ (v1_relat_1 @ X19)
% 1.13/1.36          | (v1_xboole_0 @ X19))),
% 1.13/1.36      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.13/1.36  thf('56', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.13/1.36          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['54', '55'])).
% 1.13/1.36  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('58', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.13/1.36          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['56', '57'])).
% 1.13/1.36  thf('59', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['0', '58'])).
% 1.13/1.36  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.13/1.36      inference('sup-', [status(thm)], ['17', '52'])).
% 1.13/1.36  thf('61', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('demod', [status(thm)], ['59', '60'])).
% 1.13/1.36  thf('62', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('simplify', [status(thm)], ['61'])).
% 1.13/1.36  thf('63', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('65', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.13/1.36      inference('demod', [status(thm)], ['28', '29'])).
% 1.13/1.36  thf('66', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0)
% 1.13/1.36          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.13/1.36             k1_xboole_0))),
% 1.13/1.36      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.36  thf('67', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0)
% 1.13/1.36          | ~ (v1_relat_1 @ X0))),
% 1.13/1.36      inference('sup+', [status(thm)], ['65', '66'])).
% 1.13/1.36  thf('68', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0) | (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 1.13/1.36      inference('simplify', [status(thm)], ['67'])).
% 1.13/1.36  thf('69', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('sup-', [status(thm)], ['64', '68'])).
% 1.13/1.36  thf('70', plain,
% 1.13/1.36      (![X0 : $i]: ((r1_tarski @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.36      inference('sup+', [status(thm)], ['63', '69'])).
% 1.13/1.36  thf('71', plain,
% 1.13/1.36      (![X13 : $i, X14 : $i]:
% 1.13/1.36         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.13/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.13/1.36  thf('72', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['70', '71'])).
% 1.13/1.36  thf('73', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('74', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('75', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.36      inference('sup+', [status(thm)], ['73', '74'])).
% 1.13/1.36  thf('76', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.13/1.36      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.36  thf('77', plain,
% 1.13/1.36      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.13/1.36        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('78', plain,
% 1.13/1.36      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('split', [status(esa)], ['77'])).
% 1.13/1.36  thf('79', plain,
% 1.13/1.36      ((![X0 : $i, X1 : $i]:
% 1.13/1.36          (((k5_relat_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.13/1.36           | ~ (v1_xboole_0 @ X0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['76', '78'])).
% 1.13/1.36  thf('80', plain,
% 1.13/1.36      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.36          (((X0) != (k1_xboole_0))
% 1.13/1.36           | ~ (v1_xboole_0 @ X0)
% 1.13/1.36           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ X2 @ X1)))
% 1.13/1.36           | ~ (v1_xboole_0 @ X1)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['75', '79'])).
% 1.13/1.36  thf('81', plain,
% 1.13/1.36      ((![X1 : $i, X2 : $i]:
% 1.13/1.36          (~ (v1_xboole_0 @ X1)
% 1.13/1.36           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ X2 @ X1)))
% 1.13/1.36           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('simplify', [status(thm)], ['80'])).
% 1.13/1.36  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('83', plain,
% 1.13/1.36      ((![X1 : $i, X2 : $i]:
% 1.13/1.36          (~ (v1_xboole_0 @ X1)
% 1.13/1.36           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ X2 @ X1)))))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('simplify_reflect+', [status(thm)], ['81', '82'])).
% 1.13/1.36  thf('84', plain,
% 1.13/1.36      ((![X0 : $i]:
% 1.13/1.36          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 1.13/1.36           | ~ (v1_xboole_0 @ X0)
% 1.13/1.36           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['72', '83'])).
% 1.13/1.36  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('86', plain,
% 1.13/1.36      ((![X0 : $i]:
% 1.13/1.36          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.13/1.36      inference('demod', [status(thm)], ['84', '85'])).
% 1.13/1.36  thf('87', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['37', '38'])).
% 1.13/1.36  thf('88', plain,
% 1.13/1.36      (![X0 : $i, X1 : $i]:
% 1.13/1.36         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.13/1.36      inference('sup+', [status(thm)], ['73', '74'])).
% 1.13/1.36  thf('89', plain,
% 1.13/1.36      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.13/1.36      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.13/1.36  thf('90', plain,
% 1.13/1.36      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.13/1.36      inference('split', [status(esa)], ['77'])).
% 1.13/1.36  thf('91', plain,
% 1.13/1.36      ((![X0 : $i]:
% 1.13/1.36          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['89', '90'])).
% 1.13/1.36  thf('92', plain,
% 1.13/1.36      ((![X0 : $i, X1 : $i]:
% 1.13/1.36          (((X0) != (k1_xboole_0))
% 1.13/1.36           | ~ (v1_xboole_0 @ X0)
% 1.13/1.36           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.13/1.36           | ~ (v1_xboole_0 @ X1)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['88', '91'])).
% 1.13/1.36  thf('93', plain,
% 1.13/1.36      ((![X1 : $i]:
% 1.13/1.36          (~ (v1_xboole_0 @ X1)
% 1.13/1.36           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.13/1.36           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.13/1.36      inference('simplify', [status(thm)], ['92'])).
% 1.13/1.36  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('95', plain,
% 1.13/1.36      ((![X1 : $i]:
% 1.13/1.36          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 1.13/1.36         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.13/1.36      inference('simplify_reflect+', [status(thm)], ['93', '94'])).
% 1.13/1.36  thf('96', plain,
% 1.13/1.36      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.13/1.36         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.13/1.36      inference('sup-', [status(thm)], ['87', '95'])).
% 1.13/1.36  thf('97', plain, ((v1_relat_1 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('99', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.13/1.36      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.13/1.36  thf('100', plain,
% 1.13/1.36      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.13/1.36       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.13/1.36      inference('split', [status(esa)], ['77'])).
% 1.13/1.36  thf('101', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.13/1.36      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 1.13/1.36  thf('102', plain,
% 1.13/1.36      (![X0 : $i]:
% 1.13/1.36         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.13/1.36      inference('simpl_trail', [status(thm)], ['86', '101'])).
% 1.13/1.36  thf('103', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.13/1.36      inference('sup-', [status(thm)], ['62', '102'])).
% 1.13/1.36  thf('104', plain, ((v1_relat_1 @ sk_A)),
% 1.13/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.36  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.13/1.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.13/1.36  thf('106', plain, ($false),
% 1.13/1.36      inference('demod', [status(thm)], ['103', '104', '105'])).
% 1.13/1.36  
% 1.13/1.36  % SZS output end Refutation
% 1.13/1.36  
% 1.13/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
