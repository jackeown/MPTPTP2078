%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bFkLKgdCu2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:34 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 379 expanded)
%              Number of leaves         :   26 ( 127 expanded)
%              Depth                    :   29
%              Number of atoms          :  838 (2513 expanded)
%              Number of equality atoms :   57 ( 153 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
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
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['53'])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','12','55'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','60'])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','54'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('69',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('82',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('93',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['78','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['96','97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bFkLKgdCu2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.98/1.21  % Solved by: fo/fo7.sh
% 0.98/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.21  % done 1338 iterations in 0.757s
% 0.98/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.98/1.21  % SZS output start Refutation
% 0.98/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.98/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.98/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.98/1.21  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.98/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.98/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 0.98/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.98/1.21  thf(dt_k5_relat_1, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.98/1.21       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.98/1.21  thf('0', plain,
% 0.98/1.21      (![X12 : $i, X13 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X12)
% 0.98/1.21          | ~ (v1_relat_1 @ X13)
% 0.98/1.21          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.98/1.21      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.98/1.21  thf(t60_relat_1, axiom,
% 0.98/1.21    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.98/1.21     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.98/1.21  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.98/1.21      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.98/1.21  thf(t45_relat_1, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( v1_relat_1 @ A ) =>
% 0.98/1.21       ( ![B:$i]:
% 0.98/1.21         ( ( v1_relat_1 @ B ) =>
% 0.98/1.21           ( r1_tarski @
% 0.98/1.21             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.98/1.21  thf('2', plain,
% 0.98/1.21      (![X18 : $i, X19 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X18)
% 0.98/1.21          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 0.98/1.21             (k2_relat_1 @ X18))
% 0.98/1.21          | ~ (v1_relat_1 @ X19))),
% 0.98/1.21      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.98/1.21  thf(t28_xboole_1, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.98/1.21  thf('3', plain,
% 0.98/1.21      (![X8 : $i, X9 : $i]:
% 0.98/1.21         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.98/1.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.98/1.21  thf('4', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X1)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.98/1.21              (k2_relat_1 @ X0)) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 0.98/1.21  thf('5', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.98/1.21            k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.98/1.21          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('sup+', [status(thm)], ['1', '4'])).
% 0.98/1.21  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.98/1.21  thf('6', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.98/1.21  thf(d1_xboole_0, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.21  thf('7', plain,
% 0.98/1.21      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.98/1.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.98/1.21  thf(t4_xboole_0, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.98/1.21            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.98/1.21       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.98/1.21            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.98/1.21  thf('8', plain,
% 0.98/1.21      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.98/1.21         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.98/1.21          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.98/1.21      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.98/1.21  thf('9', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 0.98/1.21  thf('10', plain,
% 0.98/1.21      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['6', '9'])).
% 0.98/1.21  thf(l13_xboole_0, axiom,
% 0.98/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.98/1.21  thf('11', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('12', plain,
% 0.98/1.21      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 0.98/1.21  thf(t62_relat_1, conjecture,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( v1_relat_1 @ A ) =>
% 0.98/1.21       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.98/1.21         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.98/1.21  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.21    (~( ![A:$i]:
% 0.98/1.21        ( ( v1_relat_1 @ A ) =>
% 0.98/1.21          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.98/1.21            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.98/1.21    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.98/1.21  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.21  thf(cc1_relat_1, axiom,
% 0.98/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.98/1.21  thf('14', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.98/1.21      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.98/1.21  thf('15', plain,
% 0.98/1.21      (![X12 : $i, X13 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X12)
% 0.98/1.21          | ~ (v1_relat_1 @ X13)
% 0.98/1.21          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.98/1.21      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.98/1.21  thf('16', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.98/1.21      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.98/1.21  thf('17', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.98/1.21      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.98/1.21  thf(t44_relat_1, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( v1_relat_1 @ A ) =>
% 0.98/1.21       ( ![B:$i]:
% 0.98/1.21         ( ( v1_relat_1 @ B ) =>
% 0.98/1.21           ( r1_tarski @
% 0.98/1.21             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.98/1.21  thf('18', plain,
% 0.98/1.21      (![X16 : $i, X17 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X16)
% 0.98/1.21          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 0.98/1.21             (k1_relat_1 @ X17))
% 0.98/1.21          | ~ (v1_relat_1 @ X17))),
% 0.98/1.21      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.98/1.21  thf('19', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.98/1.21           k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('sup+', [status(thm)], ['17', '18'])).
% 0.98/1.21  thf('20', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.98/1.21             k1_xboole_0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['16', '19'])).
% 0.98/1.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.98/1.21  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('22', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.98/1.21             k1_xboole_0))),
% 0.98/1.21      inference('demod', [status(thm)], ['20', '21'])).
% 0.98/1.21  thf('23', plain,
% 0.98/1.21      (![X8 : $i, X9 : $i]:
% 0.98/1.21         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.98/1.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.98/1.21  thf('24', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.98/1.21              k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['22', '23'])).
% 0.98/1.21  thf('25', plain,
% 0.98/1.21      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 0.98/1.21  thf('26', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.98/1.21      inference('demod', [status(thm)], ['24', '25'])).
% 0.98/1.21  thf(fc8_relat_1, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.98/1.21       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.98/1.21  thf('27', plain,
% 0.98/1.21      (![X14 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ (k1_relat_1 @ X14))
% 0.98/1.21          | ~ (v1_relat_1 @ X14)
% 0.98/1.21          | (v1_xboole_0 @ X14))),
% 0.98/1.21      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.98/1.21  thf('28', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.98/1.21          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.21  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('30', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.98/1.21          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('demod', [status(thm)], ['28', '29'])).
% 0.98/1.21  thf('31', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['15', '30'])).
% 0.98/1.21  thf('32', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.98/1.21          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['31'])).
% 0.98/1.21  thf('33', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['14', '32'])).
% 0.98/1.21  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('35', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('demod', [status(thm)], ['33', '34'])).
% 0.98/1.21  thf('36', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('37', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.98/1.21  thf('38', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.21      inference('sup+', [status(thm)], ['36', '37'])).
% 0.98/1.21  thf('39', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (r1_xboole_0 @ X1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['35', '38'])).
% 0.98/1.21  thf('40', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 0.98/1.21  thf('41', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['39', '40'])).
% 0.98/1.21  thf('42', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.98/1.21      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.98/1.21  thf('43', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('44', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('demod', [status(thm)], ['33', '34'])).
% 0.98/1.21  thf('45', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('46', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['44', '45'])).
% 0.98/1.21  thf('47', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.98/1.21          | ~ (v1_xboole_0 @ X0)
% 0.98/1.21          | ~ (v1_relat_1 @ X1))),
% 0.98/1.21      inference('sup+', [status(thm)], ['43', '46'])).
% 0.98/1.21  thf('48', plain,
% 0.98/1.21      (![X12 : $i, X13 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X12)
% 0.98/1.21          | ~ (v1_relat_1 @ X13)
% 0.98/1.21          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.98/1.21      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.98/1.21  thf('49', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | ~ (v1_xboole_0 @ X1)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | ~ (v1_relat_1 @ X1))),
% 0.98/1.21      inference('sup+', [status(thm)], ['47', '48'])).
% 0.98/1.21  thf('50', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X1)
% 0.98/1.21          | ~ (v1_xboole_0 @ X1)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_relat_1 @ k1_xboole_0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['49'])).
% 0.98/1.21  thf('51', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ X0)
% 0.98/1.21          | (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X1)
% 0.98/1.21          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['42', '50'])).
% 0.98/1.21  thf('52', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X1)
% 0.98/1.21          | (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['51'])).
% 0.98/1.21  thf('53', plain,
% 0.98/1.21      (![X0 : $i, X2 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X2))),
% 0.98/1.21      inference('sup-', [status(thm)], ['41', '52'])).
% 0.98/1.21  thf('54', plain,
% 0.98/1.21      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.98/1.21      inference('condensation', [status(thm)], ['53'])).
% 0.98/1.21  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.98/1.21      inference('sup-', [status(thm)], ['13', '54'])).
% 0.98/1.21  thf('56', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('demod', [status(thm)], ['5', '12', '55'])).
% 0.98/1.21  thf(fc9_relat_1, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.98/1.21       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.98/1.21  thf('57', plain,
% 0.98/1.21      (![X15 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 0.98/1.21          | ~ (v1_relat_1 @ X15)
% 0.98/1.21          | (v1_xboole_0 @ X15))),
% 0.98/1.21      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.98/1.21  thf('58', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.98/1.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['56', '57'])).
% 0.98/1.21  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('60', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.98/1.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.98/1.21      inference('demod', [status(thm)], ['58', '59'])).
% 0.98/1.21  thf('61', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ k1_xboole_0)
% 0.98/1.21          | ~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['0', '60'])).
% 0.98/1.21  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.98/1.21      inference('sup-', [status(thm)], ['13', '54'])).
% 0.98/1.21  thf('63', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0)
% 0.98/1.21          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.98/1.21          | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('demod', [status(thm)], ['61', '62'])).
% 0.98/1.21  thf('64', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['63'])).
% 0.98/1.21  thf('65', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('66', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('67', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.21      inference('sup+', [status(thm)], ['65', '66'])).
% 0.98/1.21  thf('68', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.21      inference('sup+', [status(thm)], ['65', '66'])).
% 0.98/1.21  thf('69', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('70', plain,
% 0.98/1.21      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.98/1.21        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.21  thf('71', plain,
% 0.98/1.21      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('split', [status(esa)], ['70'])).
% 0.98/1.21  thf('72', plain,
% 0.98/1.21      ((![X0 : $i]:
% 0.98/1.21          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['69', '71'])).
% 0.98/1.21  thf('73', plain,
% 0.98/1.21      ((![X0 : $i, X1 : $i]:
% 0.98/1.21          (((X0) != (k1_xboole_0))
% 0.98/1.21           | ~ (v1_xboole_0 @ X0)
% 0.98/1.21           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.98/1.21           | ~ (v1_xboole_0 @ X1)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['68', '72'])).
% 0.98/1.21  thf('74', plain,
% 0.98/1.21      ((![X1 : $i]:
% 0.98/1.21          (~ (v1_xboole_0 @ X1)
% 0.98/1.21           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.98/1.21           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('simplify', [status(thm)], ['73'])).
% 0.98/1.21  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('76', plain,
% 0.98/1.21      ((![X1 : $i]:
% 0.98/1.21          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('simplify_reflect+', [status(thm)], ['74', '75'])).
% 0.98/1.21  thf('77', plain,
% 0.98/1.21      ((![X0 : $i, X1 : $i]:
% 0.98/1.21          (~ (v1_xboole_0 @ X0)
% 0.98/1.21           | ~ (v1_xboole_0 @ X0)
% 0.98/1.21           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.98/1.21           | ~ (v1_xboole_0 @ X1)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['67', '76'])).
% 0.98/1.21  thf('78', plain,
% 0.98/1.21      ((![X0 : $i, X1 : $i]:
% 0.98/1.21          (~ (v1_xboole_0 @ X1)
% 0.98/1.21           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.98/1.21           | ~ (v1_xboole_0 @ X0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.98/1.21      inference('simplify', [status(thm)], ['77'])).
% 0.98/1.21  thf('79', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.98/1.21      inference('demod', [status(thm)], ['33', '34'])).
% 0.98/1.21  thf('80', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.21      inference('sup+', [status(thm)], ['65', '66'])).
% 0.98/1.21  thf('81', plain,
% 0.98/1.21      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.98/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.98/1.21  thf('82', plain,
% 0.98/1.21      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.98/1.21      inference('split', [status(esa)], ['70'])).
% 0.98/1.21  thf('83', plain,
% 0.98/1.21      ((![X0 : $i]:
% 0.98/1.21          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['81', '82'])).
% 0.98/1.21  thf('84', plain,
% 0.98/1.21      ((![X0 : $i, X1 : $i]:
% 0.98/1.21          (((X0) != (k1_xboole_0))
% 0.98/1.21           | ~ (v1_xboole_0 @ X0)
% 0.98/1.21           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.98/1.21           | ~ (v1_xboole_0 @ X1)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['80', '83'])).
% 0.98/1.21  thf('85', plain,
% 0.98/1.21      ((![X1 : $i]:
% 0.98/1.21          (~ (v1_xboole_0 @ X1)
% 0.98/1.21           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.98/1.21           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.98/1.21      inference('simplify', [status(thm)], ['84'])).
% 0.98/1.21  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('87', plain,
% 0.98/1.21      ((![X1 : $i]:
% 0.98/1.21          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.98/1.21         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.98/1.21      inference('simplify_reflect+', [status(thm)], ['85', '86'])).
% 0.98/1.21  thf('88', plain,
% 0.98/1.21      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.98/1.21         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['79', '87'])).
% 0.98/1.21  thf('89', plain, ((v1_relat_1 @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.21  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('91', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.98/1.21      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.98/1.21  thf('92', plain,
% 0.98/1.21      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.98/1.21       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.98/1.21      inference('split', [status(esa)], ['70'])).
% 0.98/1.21  thf('93', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.98/1.21      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.98/1.21  thf('94', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ X1)
% 0.98/1.21          | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.98/1.21          | ~ (v1_xboole_0 @ X0))),
% 0.98/1.21      inference('simpl_trail', [status(thm)], ['78', '93'])).
% 0.98/1.21  thf('95', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)))),
% 0.98/1.21      inference('condensation', [status(thm)], ['94'])).
% 0.98/1.21  thf('96', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['64', '95'])).
% 0.98/1.21  thf('97', plain, ((v1_relat_1 @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.21  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.21  thf('99', plain, ($false),
% 0.98/1.21      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.98/1.21  
% 0.98/1.21  % SZS output end Refutation
% 0.98/1.21  
% 0.98/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
