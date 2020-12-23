%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1zphHKMqg2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:33 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 337 expanded)
%              Number of leaves         :   28 ( 114 expanded)
%              Depth                    :   31
%              Number of atoms          :  759 (2243 expanded)
%              Number of equality atoms :   47 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

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

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','43'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

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

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('73',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('85',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['70','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['87','88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1zphHKMqg2
% 0.14/0.38  % Computer   : n013.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 15:20:55 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.85/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.05  % Solved by: fo/fo7.sh
% 0.85/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.05  % done 974 iterations in 0.555s
% 0.85/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.05  % SZS output start Refutation
% 0.85/1.05  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.85/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.85/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.85/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.85/1.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.85/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.85/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.85/1.05  thf(dt_k5_relat_1, axiom,
% 0.85/1.05    (![A:$i,B:$i]:
% 0.85/1.05     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.85/1.05       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.85/1.05  thf('0', plain,
% 0.85/1.05      (![X16 : $i, X17 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X16)
% 0.85/1.05          | ~ (v1_relat_1 @ X17)
% 0.85/1.05          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 0.85/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.85/1.05  thf(t60_relat_1, axiom,
% 0.85/1.05    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.85/1.05     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.85/1.05  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.05      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.85/1.05  thf(t45_relat_1, axiom,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( v1_relat_1 @ A ) =>
% 0.85/1.05       ( ![B:$i]:
% 0.85/1.05         ( ( v1_relat_1 @ B ) =>
% 0.85/1.05           ( r1_tarski @
% 0.85/1.05             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.85/1.05  thf('2', plain,
% 0.85/1.05      (![X22 : $i, X23 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X22)
% 0.85/1.05          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X23 @ X22)) @ 
% 0.85/1.05             (k2_relat_1 @ X22))
% 0.85/1.05          | ~ (v1_relat_1 @ X23))),
% 0.85/1.05      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.85/1.05  thf('3', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.85/1.05           k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.85/1.05      inference('sup+', [status(thm)], ['1', '2'])).
% 0.85/1.05  thf(t62_relat_1, conjecture,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( v1_relat_1 @ A ) =>
% 0.85/1.05       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.85/1.05         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.85/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.05    (~( ![A:$i]:
% 0.85/1.05        ( ( v1_relat_1 @ A ) =>
% 0.85/1.05          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.85/1.05            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.85/1.05    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.85/1.05  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf(cc1_relat_1, axiom,
% 0.85/1.05    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.85/1.05  thf('5', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.85/1.05      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.85/1.05  thf('6', plain,
% 0.85/1.05      (![X16 : $i, X17 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X16)
% 0.85/1.05          | ~ (v1_relat_1 @ X17)
% 0.85/1.05          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 0.85/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.85/1.05  thf('7', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.85/1.05      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.85/1.05  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.05      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.85/1.05  thf(t44_relat_1, axiom,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( v1_relat_1 @ A ) =>
% 0.85/1.05       ( ![B:$i]:
% 0.85/1.05         ( ( v1_relat_1 @ B ) =>
% 0.85/1.05           ( r1_tarski @
% 0.85/1.05             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.85/1.05  thf('9', plain,
% 0.85/1.05      (![X20 : $i, X21 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X20)
% 0.85/1.05          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X21 @ X20)) @ 
% 0.85/1.05             (k1_relat_1 @ X21))
% 0.85/1.05          | ~ (v1_relat_1 @ X21))),
% 0.85/1.05      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.85/1.05  thf('10', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.85/1.05           k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('sup+', [status(thm)], ['8', '9'])).
% 0.85/1.05  thf('11', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.85/1.05             k1_xboole_0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['7', '10'])).
% 0.85/1.05  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.85/1.05  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('13', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.85/1.05             k1_xboole_0))),
% 0.85/1.05      inference('demod', [status(thm)], ['11', '12'])).
% 0.85/1.05  thf(t85_xboole_1, axiom,
% 0.85/1.05    (![A:$i,B:$i,C:$i]:
% 0.85/1.05     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.85/1.05  thf('14', plain,
% 0.85/1.05      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.05         (~ (r1_tarski @ X10 @ X11)
% 0.85/1.05          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.85/1.05      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.85/1.05  thf('15', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (r1_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.85/1.05             (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.05  thf(t3_boole, axiom,
% 0.85/1.05    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.85/1.05  thf('16', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.85/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.85/1.05  thf('17', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (r1_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.85/1.05      inference('demod', [status(thm)], ['15', '16'])).
% 0.85/1.05  thf(d1_xboole_0, axiom,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.85/1.05  thf('18', plain,
% 0.85/1.05      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.85/1.05      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.85/1.05  thf(idempotence_k3_xboole_0, axiom,
% 0.85/1.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.85/1.05  thf('19', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.85/1.05      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.85/1.05  thf(t4_xboole_0, axiom,
% 0.85/1.05    (![A:$i,B:$i]:
% 0.85/1.05     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.85/1.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.85/1.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.85/1.05            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.85/1.05  thf('20', plain,
% 0.85/1.05      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.85/1.05         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.85/1.05          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.85/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.85/1.05  thf('21', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.85/1.05  thf('22', plain,
% 0.85/1.05      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['18', '21'])).
% 0.85/1.05  thf('23', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['17', '22'])).
% 0.85/1.05  thf(fc8_relat_1, axiom,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.85/1.05       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.85/1.05  thf('24', plain,
% 0.85/1.05      (![X18 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ (k1_relat_1 @ X18))
% 0.85/1.05          | ~ (v1_relat_1 @ X18)
% 0.85/1.05          | (v1_xboole_0 @ X18))),
% 0.85/1.05      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.85/1.05  thf('25', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.85/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['23', '24'])).
% 0.85/1.05  thf('26', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.85/1.05          | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['6', '25'])).
% 0.85/1.05  thf('27', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.85/1.05          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('simplify', [status(thm)], ['26'])).
% 0.85/1.05  thf('28', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['5', '27'])).
% 0.85/1.05  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('30', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.85/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.05  thf('31', plain, (![X15 : $i]: ((v1_relat_1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.85/1.05      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.85/1.05  thf(l13_xboole_0, axiom,
% 0.85/1.05    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.85/1.05  thf('32', plain,
% 0.85/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.85/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.05  thf('33', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.85/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.05  thf('34', plain,
% 0.85/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.85/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.05  thf('35', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['33', '34'])).
% 0.85/1.05  thf('36', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.85/1.05          | ~ (v1_xboole_0 @ X0)
% 0.85/1.05          | ~ (v1_relat_1 @ X1))),
% 0.85/1.05      inference('sup+', [status(thm)], ['32', '35'])).
% 0.85/1.05  thf('37', plain,
% 0.85/1.05      (![X16 : $i, X17 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X16)
% 0.85/1.05          | ~ (v1_relat_1 @ X17)
% 0.85/1.05          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 0.85/1.05      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.85/1.05  thf('38', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         ((v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | ~ (v1_xboole_0 @ X1)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | ~ (v1_relat_1 @ X1))),
% 0.85/1.05      inference('sup+', [status(thm)], ['36', '37'])).
% 0.85/1.05  thf('39', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X1)
% 0.85/1.05          | ~ (v1_xboole_0 @ X1)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_relat_1 @ k1_xboole_0))),
% 0.85/1.05      inference('simplify', [status(thm)], ['38'])).
% 0.85/1.05  thf('40', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ X0)
% 0.85/1.05          | (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X1)
% 0.85/1.05          | ~ (v1_xboole_0 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['31', '39'])).
% 0.85/1.05  thf('41', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X1)
% 0.85/1.05          | (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_xboole_0 @ X0))),
% 0.85/1.05      inference('simplify', [status(thm)], ['40'])).
% 0.85/1.05  thf('42', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X1))),
% 0.85/1.05      inference('sup-', [status(thm)], ['30', '41'])).
% 0.85/1.05  thf('43', plain,
% 0.85/1.05      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.85/1.05      inference('condensation', [status(thm)], ['42'])).
% 0.85/1.05  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.85/1.05      inference('sup-', [status(thm)], ['4', '43'])).
% 0.85/1.05  thf('45', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.85/1.05           k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('demod', [status(thm)], ['3', '44'])).
% 0.85/1.05  thf('46', plain,
% 0.85/1.05      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.05         (~ (r1_tarski @ X10 @ X11)
% 0.85/1.05          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.85/1.05      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.85/1.05  thf('47', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (r1_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.85/1.05             (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['45', '46'])).
% 0.85/1.05  thf('48', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.85/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.85/1.05  thf('49', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (r1_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ X1))),
% 0.85/1.05      inference('demod', [status(thm)], ['47', '48'])).
% 0.85/1.05  thf('50', plain,
% 0.85/1.05      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['18', '21'])).
% 0.85/1.05  thf('51', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['49', '50'])).
% 0.85/1.05  thf(fc9_relat_1, axiom,
% 0.85/1.05    (![A:$i]:
% 0.85/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.85/1.05       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.85/1.05  thf('52', plain,
% 0.85/1.05      (![X19 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ (k2_relat_1 @ X19))
% 0.85/1.05          | ~ (v1_relat_1 @ X19)
% 0.85/1.05          | (v1_xboole_0 @ X19))),
% 0.85/1.05      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.85/1.05  thf('53', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.85/1.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.85/1.05      inference('sup-', [status(thm)], ['51', '52'])).
% 0.85/1.05  thf('54', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ k1_xboole_0)
% 0.85/1.05          | ~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.85/1.05          | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['0', '53'])).
% 0.85/1.05  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.85/1.05      inference('sup-', [status(thm)], ['4', '43'])).
% 0.85/1.05  thf('56', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0)
% 0.85/1.05          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.85/1.05          | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('demod', [status(thm)], ['54', '55'])).
% 0.85/1.05  thf('57', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.85/1.05      inference('simplify', [status(thm)], ['56'])).
% 0.85/1.05  thf('58', plain,
% 0.85/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.85/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.05  thf('59', plain,
% 0.85/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.85/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.05  thf('60', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.85/1.05      inference('sup+', [status(thm)], ['58', '59'])).
% 0.85/1.05  thf('61', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.85/1.05      inference('sup+', [status(thm)], ['58', '59'])).
% 0.85/1.05  thf('62', plain,
% 0.85/1.05      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.85/1.05        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('63', plain,
% 0.85/1.05      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.85/1.05      inference('split', [status(esa)], ['62'])).
% 0.85/1.05  thf('64', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          (((X0) != (k1_xboole_0))
% 0.85/1.05           | ~ (v1_xboole_0 @ X0)
% 0.85/1.05           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.85/1.05         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['61', '63'])).
% 0.85/1.05  thf('65', plain,
% 0.85/1.05      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.85/1.05         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.85/1.05      inference('simplify', [status(thm)], ['64'])).
% 0.85/1.05  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('67', plain,
% 0.85/1.05      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.85/1.05      inference('simplify_reflect+', [status(thm)], ['65', '66'])).
% 0.85/1.05  thf('68', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.85/1.05           | ~ (v1_xboole_0 @ X0)
% 0.85/1.05           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['60', '67'])).
% 0.85/1.05  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('70', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.85/1.05      inference('demod', [status(thm)], ['68', '69'])).
% 0.85/1.05  thf('71', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.85/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.05  thf('72', plain,
% 0.85/1.05      (![X0 : $i, X1 : $i]:
% 0.85/1.05         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.85/1.05      inference('sup+', [status(thm)], ['58', '59'])).
% 0.85/1.05  thf('73', plain,
% 0.85/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.85/1.05      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.05  thf('74', plain,
% 0.85/1.05      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.85/1.05      inference('split', [status(esa)], ['62'])).
% 0.85/1.05  thf('75', plain,
% 0.85/1.05      ((![X0 : $i]:
% 0.85/1.05          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['73', '74'])).
% 0.85/1.05  thf('76', plain,
% 0.85/1.05      ((![X0 : $i, X1 : $i]:
% 0.85/1.05          (((X0) != (k1_xboole_0))
% 0.85/1.05           | ~ (v1_xboole_0 @ X0)
% 0.85/1.05           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.85/1.05           | ~ (v1_xboole_0 @ X1)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['72', '75'])).
% 0.85/1.05  thf('77', plain,
% 0.85/1.05      ((![X1 : $i]:
% 0.85/1.05          (~ (v1_xboole_0 @ X1)
% 0.85/1.05           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.85/1.05           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.85/1.05      inference('simplify', [status(thm)], ['76'])).
% 0.85/1.05  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('79', plain,
% 0.85/1.05      ((![X1 : $i]:
% 0.85/1.05          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.85/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.85/1.05      inference('simplify_reflect+', [status(thm)], ['77', '78'])).
% 0.85/1.05  thf('80', plain,
% 0.85/1.05      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.85/1.05         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.85/1.05      inference('sup-', [status(thm)], ['71', '79'])).
% 0.85/1.05  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('83', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.85/1.05      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.85/1.05  thf('84', plain,
% 0.85/1.05      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.85/1.05       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.85/1.05      inference('split', [status(esa)], ['62'])).
% 0.85/1.05  thf('85', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.85/1.05      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.85/1.05  thf('86', plain,
% 0.85/1.05      (![X0 : $i]:
% 0.85/1.05         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.85/1.05      inference('simpl_trail', [status(thm)], ['70', '85'])).
% 0.85/1.05  thf('87', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.85/1.05      inference('sup-', [status(thm)], ['57', '86'])).
% 0.85/1.05  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.85/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.05  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.05  thf('90', plain, ($false),
% 0.85/1.05      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.85/1.05  
% 0.85/1.05  % SZS output end Refutation
% 0.85/1.05  
% 0.85/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
