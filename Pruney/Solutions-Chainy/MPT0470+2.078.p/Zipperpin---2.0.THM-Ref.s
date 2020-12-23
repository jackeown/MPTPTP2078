%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnzlXBEif0

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:37 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 336 expanded)
%              Number of leaves         :   26 ( 113 expanded)
%              Depth                    :   31
%              Number of atoms          :  764 (2255 expanded)
%              Number of equality atoms :   54 ( 150 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
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
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnzlXBEif0
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:25:42 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.05/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.26  % Solved by: fo/fo7.sh
% 1.05/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.26  % done 788 iterations in 0.761s
% 1.05/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.26  % SZS output start Refutation
% 1.05/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.26  thf(sk_B_type, type, sk_B: $i > $i).
% 1.05/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.26  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.05/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.26  thf(dt_k5_relat_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.05/1.26       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.05/1.26  thf('0', plain,
% 1.05/1.26      (![X10 : $i, X11 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X10)
% 1.05/1.26          | ~ (v1_relat_1 @ X11)
% 1.05/1.26          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.05/1.26  thf(t60_relat_1, axiom,
% 1.05/1.26    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.05/1.26     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.05/1.26  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.26      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.05/1.26  thf(t45_relat_1, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ A ) =>
% 1.05/1.26       ( ![B:$i]:
% 1.05/1.26         ( ( v1_relat_1 @ B ) =>
% 1.05/1.26           ( r1_tarski @
% 1.05/1.26             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.05/1.26  thf('2', plain,
% 1.05/1.26      (![X16 : $i, X17 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X16)
% 1.05/1.26          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 1.05/1.26             (k2_relat_1 @ X16))
% 1.05/1.26          | ~ (v1_relat_1 @ X17))),
% 1.05/1.26      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.05/1.26  thf('3', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.05/1.26           k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.05/1.26      inference('sup+', [status(thm)], ['1', '2'])).
% 1.05/1.26  thf(t62_relat_1, conjecture,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ A ) =>
% 1.05/1.26       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.05/1.26         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.05/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.26    (~( ![A:$i]:
% 1.05/1.26        ( ( v1_relat_1 @ A ) =>
% 1.05/1.26          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.05/1.26            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.05/1.26    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.05/1.26  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(cc1_relat_1, axiom,
% 1.05/1.26    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.05/1.26  thf('5', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 1.05/1.26      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.05/1.26  thf('6', plain,
% 1.05/1.26      (![X10 : $i, X11 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X10)
% 1.05/1.26          | ~ (v1_relat_1 @ X11)
% 1.05/1.26          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.05/1.26  thf('7', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 1.05/1.26      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.05/1.26  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.26      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.05/1.26  thf(t44_relat_1, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ A ) =>
% 1.05/1.26       ( ![B:$i]:
% 1.05/1.26         ( ( v1_relat_1 @ B ) =>
% 1.05/1.26           ( r1_tarski @
% 1.05/1.26             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.05/1.26  thf('9', plain,
% 1.05/1.26      (![X14 : $i, X15 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X14)
% 1.05/1.26          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 1.05/1.26             (k1_relat_1 @ X15))
% 1.05/1.26          | ~ (v1_relat_1 @ X15))),
% 1.05/1.26      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.05/1.26  thf('10', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.05/1.26           k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('sup+', [status(thm)], ['8', '9'])).
% 1.05/1.26  thf('11', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.05/1.26             k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['7', '10'])).
% 1.05/1.26  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.05/1.26  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('13', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.05/1.26             k1_xboole_0))),
% 1.05/1.26      inference('demod', [status(thm)], ['11', '12'])).
% 1.05/1.26  thf(t28_xboole_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.05/1.26  thf('14', plain,
% 1.05/1.26      (![X6 : $i, X7 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.26  thf('15', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 1.05/1.26              k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['13', '14'])).
% 1.05/1.26  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.05/1.26  thf('16', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.05/1.26  thf(t7_xboole_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.05/1.26          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.05/1.26  thf('17', plain,
% 1.05/1.26      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 1.05/1.26      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.05/1.26  thf(t4_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.05/1.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.05/1.26            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.05/1.26  thf('18', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 1.05/1.26          | ~ (r1_xboole_0 @ X1 @ X4))),
% 1.05/1.26      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.05/1.26  thf('19', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.26  thf('20', plain,
% 1.05/1.26      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['16', '19'])).
% 1.05/1.26  thf('21', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 1.05/1.26      inference('demod', [status(thm)], ['15', '20'])).
% 1.05/1.26  thf(fc8_relat_1, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.05/1.26       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.05/1.26  thf('22', plain,
% 1.05/1.26      (![X12 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ (k1_relat_1 @ X12))
% 1.05/1.26          | ~ (v1_relat_1 @ X12)
% 1.05/1.26          | (v1_xboole_0 @ X12))),
% 1.05/1.26      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.05/1.26  thf('23', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.05/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.26  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('25', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.05/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['23', '24'])).
% 1.05/1.26  thf('26', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['6', '25'])).
% 1.05/1.26  thf('27', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.05/1.26          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['26'])).
% 1.05/1.26  thf('28', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['5', '27'])).
% 1.05/1.26  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('30', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['28', '29'])).
% 1.05/1.26  thf('31', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 1.05/1.26      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.05/1.26  thf(l13_xboole_0, axiom,
% 1.05/1.26    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.26  thf('32', plain,
% 1.05/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.26  thf('33', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['28', '29'])).
% 1.05/1.26  thf('34', plain,
% 1.05/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.26  thf('35', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.05/1.26  thf('36', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 1.05/1.26          | ~ (v1_xboole_0 @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['32', '35'])).
% 1.05/1.26  thf('37', plain,
% 1.05/1.26      (![X10 : $i, X11 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X10)
% 1.05/1.26          | ~ (v1_relat_1 @ X11)
% 1.05/1.26          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.05/1.26  thf('38', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | ~ (v1_xboole_0 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('39', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_xboole_0 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_relat_1 @ k1_xboole_0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['38'])).
% 1.05/1.26  thf('40', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ X0)
% 1.05/1.26          | (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['31', '39'])).
% 1.05/1.26  thf('41', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X1)
% 1.05/1.26          | (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['40'])).
% 1.05/1.26  thf('42', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['30', '41'])).
% 1.05/1.26  thf('43', plain,
% 1.05/1.26      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.05/1.26      inference('condensation', [status(thm)], ['42'])).
% 1.05/1.26  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.05/1.26      inference('sup-', [status(thm)], ['4', '43'])).
% 1.05/1.26  thf('45', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.05/1.26           k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('demod', [status(thm)], ['3', '44'])).
% 1.05/1.26  thf('46', plain,
% 1.05/1.26      (![X6 : $i, X7 : $i]:
% 1.05/1.26         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.05/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.26  thf('47', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.05/1.26              k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf('48', plain,
% 1.05/1.26      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['16', '19'])).
% 1.05/1.26  thf('49', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.05/1.26      inference('demod', [status(thm)], ['47', '48'])).
% 1.05/1.26  thf(fc9_relat_1, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.05/1.26       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.05/1.26  thf('50', plain,
% 1.05/1.26      (![X13 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ (k2_relat_1 @ X13))
% 1.05/1.26          | ~ (v1_relat_1 @ X13)
% 1.05/1.26          | (v1_xboole_0 @ X13))),
% 1.05/1.26      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.05/1.26  thf('51', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['49', '50'])).
% 1.05/1.26  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('53', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['51', '52'])).
% 1.05/1.26  thf('54', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ k1_xboole_0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['0', '53'])).
% 1.05/1.26  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.05/1.26      inference('sup-', [status(thm)], ['4', '43'])).
% 1.05/1.26  thf('56', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('demod', [status(thm)], ['54', '55'])).
% 1.05/1.26  thf('57', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['56'])).
% 1.05/1.26  thf('58', plain,
% 1.05/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.26  thf('59', plain,
% 1.05/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.26  thf('60', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['58', '59'])).
% 1.05/1.26  thf('61', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['58', '59'])).
% 1.05/1.26  thf('62', plain,
% 1.05/1.26      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.05/1.26        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('63', plain,
% 1.05/1.26      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.05/1.26      inference('split', [status(esa)], ['62'])).
% 1.05/1.26  thf('64', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (((X0) != (k1_xboole_0))
% 1.05/1.26           | ~ (v1_xboole_0 @ X0)
% 1.05/1.26           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 1.05/1.26         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['61', '63'])).
% 1.05/1.26  thf('65', plain,
% 1.05/1.26      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 1.05/1.26         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.05/1.26      inference('simplify', [status(thm)], ['64'])).
% 1.05/1.26  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('67', plain,
% 1.05/1.26      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.05/1.26      inference('simplify_reflect+', [status(thm)], ['65', '66'])).
% 1.05/1.26  thf('68', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 1.05/1.26           | ~ (v1_xboole_0 @ X0)
% 1.05/1.26           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['60', '67'])).
% 1.05/1.26  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('70', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.05/1.26      inference('demod', [status(thm)], ['68', '69'])).
% 1.05/1.26  thf('71', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['28', '29'])).
% 1.05/1.26  thf('72', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['58', '59'])).
% 1.05/1.26  thf('73', plain,
% 1.05/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.05/1.26  thf('74', plain,
% 1.05/1.26      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.05/1.26      inference('split', [status(esa)], ['62'])).
% 1.05/1.26  thf('75', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['73', '74'])).
% 1.05/1.26  thf('76', plain,
% 1.05/1.26      ((![X0 : $i, X1 : $i]:
% 1.05/1.26          (((X0) != (k1_xboole_0))
% 1.05/1.26           | ~ (v1_xboole_0 @ X0)
% 1.05/1.26           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.05/1.26           | ~ (v1_xboole_0 @ X1)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['72', '75'])).
% 1.05/1.26  thf('77', plain,
% 1.05/1.26      ((![X1 : $i]:
% 1.05/1.26          (~ (v1_xboole_0 @ X1)
% 1.05/1.26           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 1.05/1.26           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.05/1.26      inference('simplify', [status(thm)], ['76'])).
% 1.05/1.26  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('79', plain,
% 1.05/1.26      ((![X1 : $i]:
% 1.05/1.26          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 1.05/1.26         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.05/1.26      inference('simplify_reflect+', [status(thm)], ['77', '78'])).
% 1.05/1.26  thf('80', plain,
% 1.05/1.26      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.05/1.26         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['71', '79'])).
% 1.05/1.26  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('83', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.05/1.26      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.05/1.26  thf('84', plain,
% 1.05/1.26      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 1.05/1.26       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.05/1.26      inference('split', [status(esa)], ['62'])).
% 1.05/1.26  thf('85', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.05/1.26      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 1.05/1.26  thf('86', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.26      inference('simpl_trail', [status(thm)], ['70', '85'])).
% 1.05/1.26  thf('87', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['57', '86'])).
% 1.05/1.26  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.26  thf('90', plain, ($false),
% 1.05/1.26      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.05/1.26  
% 1.05/1.26  % SZS output end Refutation
% 1.05/1.26  
% 1.05/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
