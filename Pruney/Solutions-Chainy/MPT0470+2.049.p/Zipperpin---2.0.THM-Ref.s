%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Apkeqtjp7k

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 342 expanded)
%              Number of leaves         :   26 ( 115 expanded)
%              Depth                    :   29
%              Number of atoms          :  736 (2270 expanded)
%              Number of equality atoms :   51 ( 138 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X8 ) ) ),
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
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

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

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('17',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','12','49'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','48'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('70',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('82',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['67','82'])).

thf('84',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Apkeqtjp7k
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.07/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.24  % Solved by: fo/fo7.sh
% 1.07/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.24  % done 1883 iterations in 0.794s
% 1.07/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.24  % SZS output start Refutation
% 1.07/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.07/1.24  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.07/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.24  thf(dt_k5_relat_1, axiom,
% 1.07/1.24    (![A:$i,B:$i]:
% 1.07/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.07/1.24       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.07/1.24  thf('0', plain,
% 1.07/1.24      (![X14 : $i, X15 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X14)
% 1.07/1.24          | ~ (v1_relat_1 @ X15)
% 1.07/1.24          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 1.07/1.24      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.24  thf(t60_relat_1, axiom,
% 1.07/1.24    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.07/1.24     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.07/1.24  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.24      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.07/1.24  thf(t45_relat_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( v1_relat_1 @ A ) =>
% 1.07/1.24       ( ![B:$i]:
% 1.07/1.24         ( ( v1_relat_1 @ B ) =>
% 1.07/1.24           ( r1_tarski @
% 1.07/1.24             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.07/1.24  thf('2', plain,
% 1.07/1.24      (![X20 : $i, X21 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X20)
% 1.07/1.24          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X21 @ X20)) @ 
% 1.07/1.24             (k2_relat_1 @ X20))
% 1.07/1.24          | ~ (v1_relat_1 @ X21))),
% 1.07/1.24      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.07/1.24  thf(t28_xboole_1, axiom,
% 1.07/1.24    (![A:$i,B:$i]:
% 1.07/1.24     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.07/1.24  thf('3', plain,
% 1.07/1.24      (![X11 : $i, X12 : $i]:
% 1.07/1.24         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.07/1.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.24  thf('4', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X1)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 1.07/1.24              (k2_relat_1 @ X0)) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['2', '3'])).
% 1.07/1.24  thf('5', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.07/1.24            k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.07/1.24          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('sup+', [status(thm)], ['1', '4'])).
% 1.07/1.24  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.07/1.24  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf(t3_xboole_0, axiom,
% 1.07/1.24    (![A:$i,B:$i]:
% 1.07/1.24     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.07/1.24            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.24       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.07/1.24            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.07/1.24  thf('7', plain,
% 1.07/1.24      (![X7 : $i, X8 : $i]:
% 1.07/1.24         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X8))),
% 1.07/1.24      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.07/1.24  thf(d1_xboole_0, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.07/1.24  thf('8', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.07/1.24      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.07/1.24  thf('9', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.07/1.24  thf('10', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.07/1.24      inference('sup-', [status(thm)], ['6', '9'])).
% 1.07/1.24  thf(d7_xboole_0, axiom,
% 1.07/1.24    (![A:$i,B:$i]:
% 1.07/1.24     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.07/1.24       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.07/1.24  thf('11', plain,
% 1.07/1.24      (![X3 : $i, X4 : $i]:
% 1.07/1.24         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 1.07/1.24      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.24  thf('12', plain,
% 1.07/1.24      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.07/1.24  thf(t62_relat_1, conjecture,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( v1_relat_1 @ A ) =>
% 1.07/1.24       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.07/1.24         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.07/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.24    (~( ![A:$i]:
% 1.07/1.24        ( ( v1_relat_1 @ A ) =>
% 1.07/1.24          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.07/1.24            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.07/1.24    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.07/1.24  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf(cc1_relat_1, axiom,
% 1.07/1.24    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.07/1.24  thf('14', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 1.07/1.24      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.07/1.24  thf('15', plain,
% 1.07/1.24      (![X14 : $i, X15 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X14)
% 1.07/1.24          | ~ (v1_relat_1 @ X15)
% 1.07/1.24          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 1.07/1.24      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.24  thf('16', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 1.07/1.24      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.07/1.24  thf('17', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.24      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.07/1.24  thf(t44_relat_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( v1_relat_1 @ A ) =>
% 1.07/1.24       ( ![B:$i]:
% 1.07/1.24         ( ( v1_relat_1 @ B ) =>
% 1.07/1.24           ( r1_tarski @
% 1.07/1.24             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.07/1.24  thf('18', plain,
% 1.07/1.24      (![X18 : $i, X19 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X18)
% 1.07/1.24          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 1.07/1.24             (k1_relat_1 @ X19))
% 1.07/1.24          | ~ (v1_relat_1 @ X19))),
% 1.07/1.24      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.07/1.24  thf('19', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.07/1.24           k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('sup+', [status(thm)], ['17', '18'])).
% 1.07/1.24  thf('20', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.07/1.24             k1_xboole_0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['16', '19'])).
% 1.07/1.24  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('22', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.07/1.24             k1_xboole_0))),
% 1.07/1.24      inference('demod', [status(thm)], ['20', '21'])).
% 1.07/1.24  thf('23', plain,
% 1.07/1.24      (![X11 : $i, X12 : $i]:
% 1.07/1.24         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.07/1.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.24  thf('24', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.07/1.24              k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['22', '23'])).
% 1.07/1.24  thf('25', plain,
% 1.07/1.24      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['10', '11'])).
% 1.07/1.24  thf('26', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.07/1.24      inference('demod', [status(thm)], ['24', '25'])).
% 1.07/1.24  thf(fc8_relat_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.07/1.24       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.07/1.24  thf('27', plain,
% 1.07/1.24      (![X16 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ (k1_relat_1 @ X16))
% 1.07/1.24          | ~ (v1_relat_1 @ X16)
% 1.07/1.24          | (v1_xboole_0 @ X16))),
% 1.07/1.24      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.07/1.24  thf('28', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.07/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['26', '27'])).
% 1.07/1.24  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('30', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.07/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.07/1.24      inference('demod', [status(thm)], ['28', '29'])).
% 1.07/1.24  thf('31', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['15', '30'])).
% 1.07/1.24  thf('32', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.07/1.24          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('simplify', [status(thm)], ['31'])).
% 1.07/1.24  thf('33', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['14', '32'])).
% 1.07/1.24  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('35', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.07/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.07/1.24  thf('36', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 1.07/1.24      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.07/1.24  thf(l13_xboole_0, axiom,
% 1.07/1.24    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.07/1.24  thf('37', plain,
% 1.07/1.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.07/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.24  thf('38', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.07/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.07/1.24  thf('39', plain,
% 1.07/1.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.07/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.24  thf('40', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['38', '39'])).
% 1.07/1.24  thf('41', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.07/1.24          | ~ (v1_xboole_0 @ X0)
% 1.07/1.24          | ~ (v1_relat_1 @ X1))),
% 1.07/1.24      inference('sup+', [status(thm)], ['37', '40'])).
% 1.07/1.24  thf('42', plain,
% 1.07/1.24      (![X14 : $i, X15 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X14)
% 1.07/1.24          | ~ (v1_relat_1 @ X15)
% 1.07/1.24          | (v1_relat_1 @ (k5_relat_1 @ X14 @ X15)))),
% 1.07/1.24      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.07/1.24  thf('43', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         ((v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | ~ (v1_xboole_0 @ X1)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | ~ (v1_relat_1 @ X1))),
% 1.07/1.24      inference('sup+', [status(thm)], ['41', '42'])).
% 1.07/1.24  thf('44', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X1)
% 1.07/1.24          | ~ (v1_xboole_0 @ X1)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_relat_1 @ k1_xboole_0))),
% 1.07/1.24      inference('simplify', [status(thm)], ['43'])).
% 1.07/1.24  thf('45', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ X0)
% 1.07/1.24          | (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X1)
% 1.07/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['36', '44'])).
% 1.07/1.24  thf('46', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X1)
% 1.07/1.24          | (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_xboole_0 @ X0))),
% 1.07/1.24      inference('simplify', [status(thm)], ['45'])).
% 1.07/1.24  thf('47', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X1))),
% 1.07/1.24      inference('sup-', [status(thm)], ['35', '46'])).
% 1.07/1.24  thf('48', plain,
% 1.07/1.24      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.07/1.24      inference('condensation', [status(thm)], ['47'])).
% 1.07/1.24  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.07/1.24      inference('sup-', [status(thm)], ['13', '48'])).
% 1.07/1.24  thf('50', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('demod', [status(thm)], ['5', '12', '49'])).
% 1.07/1.24  thf(fc9_relat_1, axiom,
% 1.07/1.24    (![A:$i]:
% 1.07/1.24     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.07/1.24       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.07/1.24  thf('51', plain,
% 1.07/1.24      (![X17 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ (k2_relat_1 @ X17))
% 1.07/1.24          | ~ (v1_relat_1 @ X17)
% 1.07/1.24          | (v1_xboole_0 @ X17))),
% 1.07/1.24      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.07/1.24  thf('52', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.07/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.07/1.24      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.24  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('54', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.07/1.24          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.07/1.24      inference('demod', [status(thm)], ['52', '53'])).
% 1.07/1.24  thf('55', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ k1_xboole_0)
% 1.07/1.24          | ~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('sup-', [status(thm)], ['0', '54'])).
% 1.07/1.24  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.07/1.24      inference('sup-', [status(thm)], ['13', '48'])).
% 1.07/1.24  thf('57', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0)
% 1.07/1.24          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.07/1.24          | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('demod', [status(thm)], ['55', '56'])).
% 1.07/1.24  thf('58', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 1.07/1.24      inference('simplify', [status(thm)], ['57'])).
% 1.07/1.24  thf('59', plain,
% 1.07/1.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.07/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.24  thf('60', plain,
% 1.07/1.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.07/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.24  thf('61', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.07/1.24      inference('sup+', [status(thm)], ['59', '60'])).
% 1.07/1.24  thf('62', plain,
% 1.07/1.24      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.07/1.24        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('63', plain,
% 1.07/1.24      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.07/1.24      inference('split', [status(esa)], ['62'])).
% 1.07/1.24  thf('64', plain,
% 1.07/1.24      ((![X0 : $i]:
% 1.07/1.24          (((X0) != (k1_xboole_0))
% 1.07/1.24           | ~ (v1_xboole_0 @ X0)
% 1.07/1.24           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 1.07/1.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['61', '63'])).
% 1.07/1.24  thf('65', plain,
% 1.07/1.24      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 1.07/1.24         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.07/1.24      inference('simplify', [status(thm)], ['64'])).
% 1.07/1.24  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('67', plain,
% 1.07/1.24      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.07/1.24      inference('simplify_reflect+', [status(thm)], ['65', '66'])).
% 1.07/1.24  thf('68', plain,
% 1.07/1.24      (![X0 : $i]:
% 1.07/1.24         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.07/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.07/1.24  thf('69', plain,
% 1.07/1.24      (![X0 : $i, X1 : $i]:
% 1.07/1.24         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.07/1.24      inference('sup+', [status(thm)], ['59', '60'])).
% 1.07/1.24  thf('70', plain,
% 1.07/1.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.07/1.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.24  thf('71', plain,
% 1.07/1.24      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.07/1.24      inference('split', [status(esa)], ['62'])).
% 1.07/1.24  thf('72', plain,
% 1.07/1.24      ((![X0 : $i]:
% 1.07/1.24          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['70', '71'])).
% 1.07/1.24  thf('73', plain,
% 1.07/1.24      ((![X0 : $i, X1 : $i]:
% 1.07/1.24          (((X0) != (k1_xboole_0))
% 1.07/1.24           | ~ (v1_xboole_0 @ X0)
% 1.07/1.24           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.07/1.24           | ~ (v1_xboole_0 @ X1)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['69', '72'])).
% 1.07/1.24  thf('74', plain,
% 1.07/1.24      ((![X1 : $i]:
% 1.07/1.24          (~ (v1_xboole_0 @ X1)
% 1.07/1.24           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.07/1.24           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.07/1.24      inference('simplify', [status(thm)], ['73'])).
% 1.07/1.24  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('76', plain,
% 1.07/1.24      ((![X1 : $i]:
% 1.07/1.24          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 1.07/1.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.07/1.24      inference('simplify_reflect+', [status(thm)], ['74', '75'])).
% 1.07/1.24  thf('77', plain,
% 1.07/1.24      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.07/1.24         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.07/1.24      inference('sup-', [status(thm)], ['68', '76'])).
% 1.07/1.24  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.24      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.24  thf('80', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.07/1.24      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.07/1.24  thf('81', plain,
% 1.07/1.24      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.07/1.24       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.07/1.24      inference('split', [status(esa)], ['62'])).
% 1.07/1.24  thf('82', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.07/1.24      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 1.07/1.24  thf('83', plain, (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))),
% 1.07/1.24      inference('simpl_trail', [status(thm)], ['67', '82'])).
% 1.07/1.24  thf('84', plain, (~ (v1_relat_1 @ sk_A)),
% 1.07/1.24      inference('sup-', [status(thm)], ['58', '83'])).
% 1.07/1.24  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 1.07/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.24  thf('86', plain, ($false), inference('demod', [status(thm)], ['84', '85'])).
% 1.07/1.24  
% 1.07/1.24  % SZS output end Refutation
% 1.07/1.24  
% 1.07/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
