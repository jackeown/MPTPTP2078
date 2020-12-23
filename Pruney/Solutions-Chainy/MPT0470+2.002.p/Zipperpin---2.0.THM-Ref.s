%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qR0sZ0r5Ai

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:26 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 323 expanded)
%              Number of leaves         :   23 ( 107 expanded)
%              Depth                    :   31
%              Number of atoms          :  706 (2116 expanded)
%              Number of equality atoms :   47 ( 125 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('71',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('80',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['68','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qR0sZ0r5Ai
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 270 iterations in 0.320s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.77  thf(dt_k5_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.58/0.77       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X12)
% 0.58/0.77          | ~ (v1_relat_1 @ X13)
% 0.58/0.77          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.77  thf(t60_relat_1, axiom,
% 0.58/0.77    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.58/0.77     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.77  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.77  thf(t45_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( v1_relat_1 @ B ) =>
% 0.58/0.77           ( r1_tarski @
% 0.58/0.77             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X18 : $i, X19 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X18)
% 0.58/0.77          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X19 @ X18)) @ 
% 0.58/0.77             (k2_relat_1 @ X18))
% 0.58/0.77          | ~ (v1_relat_1 @ X19))),
% 0.58/0.77      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.58/0.77           k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['1', '2'])).
% 0.58/0.77  thf(t62_relat_1, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.58/0.77         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( v1_relat_1 @ A ) =>
% 0.58/0.77          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.58/0.77            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.58/0.77  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(cc1_relat_1, axiom,
% 0.58/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.58/0.77  thf('5', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X12)
% 0.58/0.77          | ~ (v1_relat_1 @ X13)
% 0.58/0.77          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.77  thf('7', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.77  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.77  thf(t44_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( v1_relat_1 @ B ) =>
% 0.58/0.77           ( r1_tarski @
% 0.58/0.77             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X16)
% 0.58/0.77          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 0.58/0.77             (k1_relat_1 @ X17))
% 0.58/0.77          | ~ (v1_relat_1 @ X17))),
% 0.58/0.77      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.58/0.77           k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.58/0.77             k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['7', '10'])).
% 0.58/0.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.77  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.58/0.77             k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.77  thf(d3_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X4 : $i, X6 : $i]:
% 0.58/0.77         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf(d1_xboole_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.77  thf(d10_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X8 : $i, X10 : $i]:
% 0.58/0.77         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.58/0.77          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['13', '18'])).
% 0.58/0.77  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['19', '20'])).
% 0.58/0.77  thf(fc8_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.58/0.77       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X14 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ (k1_relat_1 @ X14))
% 0.58/0.77          | ~ (v1_relat_1 @ X14)
% 0.58/0.77          | (v1_xboole_0 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.77  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['23', '24'])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['6', '25'])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['26'])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '27'])).
% 0.58/0.77  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.77  thf('31', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.58/0.77  thf(l13_xboole_0, axiom,
% 0.58/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.58/0.77          | ~ (v1_xboole_0 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['32', '35'])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X12)
% 0.58/0.77          | ~ (v1_relat_1 @ X13)
% 0.58/0.77          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_xboole_0 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_xboole_0 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['38'])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ X0)
% 0.58/0.77          | (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_xboole_0 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['31', '39'])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X1)
% 0.58/0.77          | (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_xboole_0 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['30', '41'])).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.58/0.77      inference('condensation', [status(thm)], ['42'])).
% 0.58/0.77  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '43'])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.58/0.77           k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['3', '44'])).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.58/0.77          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.77  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['47', '48'])).
% 0.58/0.77  thf(fc9_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.58/0.77       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (![X15 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 0.58/0.77          | ~ (v1_relat_1 @ X15)
% 0.58/0.77          | (v1_xboole_0 @ X15))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.77  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '53'])).
% 0.58/0.77  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '43'])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['54', '55'])).
% 0.58/0.77  thf('57', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['56'])).
% 0.58/0.77  thf('58', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.77  thf('59', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.77  thf('61', plain,
% 0.58/0.77      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.77  thf('62', plain,
% 0.58/0.77      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.58/0.77        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('63', plain,
% 0.58/0.77      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['62'])).
% 0.58/0.77  thf('64', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['61', '63'])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      ((![X0 : $i, X1 : $i]:
% 0.58/0.77          (((X0) != (k1_xboole_0))
% 0.58/0.77           | ~ (v1_xboole_0 @ X0)
% 0.58/0.77           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.58/0.77           | ~ (v1_xboole_0 @ X1)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['60', '64'])).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      ((![X1 : $i]:
% 0.58/0.77          (~ (v1_xboole_0 @ X1)
% 0.58/0.77           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.58/0.77           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['65'])).
% 0.58/0.77  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('68', plain,
% 0.58/0.77      ((![X1 : $i]:
% 0.58/0.77          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.58/0.77         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.58/0.77      inference('simplify_reflect+', [status(thm)], ['66', '67'])).
% 0.58/0.77  thf('69', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.77  thf('71', plain,
% 0.58/0.77      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['62'])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (((X0) != (k1_xboole_0))
% 0.58/0.77           | ~ (v1_xboole_0 @ X0)
% 0.58/0.77           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))))
% 0.58/0.77         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.77  thf('73', plain,
% 0.58/0.77      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.58/0.77         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['72'])).
% 0.58/0.77  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('75', plain,
% 0.58/0.77      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 0.58/0.77         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('simplify_reflect+', [status(thm)], ['73', '74'])).
% 0.58/0.77  thf('76', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ sk_A))
% 0.58/0.77         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['69', '75'])).
% 0.58/0.77  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('78', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['76', '77'])).
% 0.58/0.77  thf('79', plain,
% 0.58/0.77      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.58/0.77       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.58/0.77      inference('split', [status(esa)], ['62'])).
% 0.58/0.77  thf('80', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.58/0.77  thf('81', plain,
% 0.58/0.77      (![X1 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1)))),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['68', '80'])).
% 0.58/0.77  thf('82', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['57', '81'])).
% 0.58/0.77  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.77  thf('85', plain, ($false),
% 0.58/0.77      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
