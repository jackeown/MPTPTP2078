%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfrBNNkRsn

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:35 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 312 expanded)
%              Number of leaves         :   26 ( 107 expanded)
%              Depth                    :   27
%              Number of atoms          :  817 (2135 expanded)
%              Number of equality atoms :   61 ( 166 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

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

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('25',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X19 @ X18 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','20','56'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','55'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

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

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('80',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('91',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['76','91'])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['93','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfrBNNkRsn
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.95  % Solved by: fo/fo7.sh
% 0.78/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.95  % done 1202 iterations in 0.503s
% 0.78/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.95  % SZS output start Refutation
% 0.78/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.78/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.78/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.78/0.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.78/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.95  thf(dt_k5_relat_1, axiom,
% 0.78/0.95    (![A:$i,B:$i]:
% 0.78/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.78/0.95       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.78/0.95  thf('0', plain,
% 0.78/0.95      (![X12 : $i, X13 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X12)
% 0.78/0.95          | ~ (v1_relat_1 @ X13)
% 0.78/0.95          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.78/0.95      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.78/0.95  thf(t60_relat_1, axiom,
% 0.78/0.95    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.78/0.95     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.78/0.95  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.78/0.95  thf(t45_relat_1, axiom,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( v1_relat_1 @ A ) =>
% 0.78/0.95       ( ![B:$i]:
% 0.78/0.95         ( ( v1_relat_1 @ B ) =>
% 0.78/0.95           ( r1_tarski @
% 0.78/0.95             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.78/0.95  thf('2', plain,
% 0.78/0.95      (![X16 : $i, X17 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X16)
% 0.78/0.95          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 0.78/0.95             (k2_relat_1 @ X16))
% 0.78/0.95          | ~ (v1_relat_1 @ X17))),
% 0.78/0.95      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.78/0.95  thf(t28_xboole_1, axiom,
% 0.78/0.95    (![A:$i,B:$i]:
% 0.78/0.95     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.78/0.95  thf('3', plain,
% 0.78/0.95      (![X8 : $i, X9 : $i]:
% 0.78/0.95         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.78/0.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.95  thf('4', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X1)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ 
% 0.78/0.95              (k2_relat_1 @ X0)) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.78/0.95  thf('5', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.78/0.95            k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.78/0.95          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('sup+', [status(thm)], ['1', '4'])).
% 0.78/0.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.78/0.95  thf('6', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.78/0.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.78/0.95  thf('7', plain,
% 0.78/0.95      (![X8 : $i, X9 : $i]:
% 0.78/0.95         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.78/0.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.95  thf('8', plain,
% 0.78/0.95      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['6', '7'])).
% 0.78/0.95  thf(d7_xboole_0, axiom,
% 0.78/0.95    (![A:$i,B:$i]:
% 0.78/0.95     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.78/0.95       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.78/0.95  thf('9', plain,
% 0.78/0.95      (![X0 : $i, X2 : $i]:
% 0.78/0.95         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.78/0.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.78/0.95  thf('10', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['8', '9'])).
% 0.78/0.95  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.78/0.95      inference('simplify', [status(thm)], ['10'])).
% 0.78/0.95  thf(t3_xboole_0, axiom,
% 0.78/0.95    (![A:$i,B:$i]:
% 0.78/0.95     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.78/0.95            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.78/0.95       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.78/0.95            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.78/0.95  thf('12', plain,
% 0.78/0.95      (![X4 : $i, X5 : $i]:
% 0.78/0.95         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.78/0.95      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.95  thf('13', plain,
% 0.78/0.95      (![X4 : $i, X5 : $i]:
% 0.78/0.95         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.78/0.95      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.95  thf('14', plain,
% 0.78/0.95      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X6 @ X4)
% 0.78/0.95          | ~ (r2_hidden @ X6 @ X7)
% 0.78/0.95          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.78/0.95      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.78/0.95  thf('15', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.95         ((r1_xboole_0 @ X1 @ X0)
% 0.78/0.95          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.78/0.95          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.78/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.78/0.95  thf('16', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         ((r1_xboole_0 @ X0 @ X1)
% 0.78/0.95          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.78/0.95          | (r1_xboole_0 @ X0 @ X1))),
% 0.78/0.95      inference('sup-', [status(thm)], ['12', '15'])).
% 0.78/0.95  thf('17', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.78/0.95      inference('simplify', [status(thm)], ['16'])).
% 0.78/0.95  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.78/0.95      inference('sup-', [status(thm)], ['11', '17'])).
% 0.78/0.95  thf('19', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.78/0.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.78/0.95  thf('20', plain,
% 0.78/0.95      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.78/0.95  thf(t62_relat_1, conjecture,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( v1_relat_1 @ A ) =>
% 0.78/0.95       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.78/0.95         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.78/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.95    (~( ![A:$i]:
% 0.78/0.95        ( ( v1_relat_1 @ A ) =>
% 0.78/0.95          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.78/0.95            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.78/0.95    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.78/0.95  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf(cc1_relat_1, axiom,
% 0.78/0.95    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.78/0.95  thf('22', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.78/0.95      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.78/0.95  thf('23', plain,
% 0.78/0.95      (![X12 : $i, X13 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X12)
% 0.78/0.95          | ~ (v1_relat_1 @ X13)
% 0.78/0.95          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.78/0.95      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.78/0.95  thf('24', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.78/0.95      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.78/0.95  thf('25', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.78/0.95  thf(t46_relat_1, axiom,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( v1_relat_1 @ A ) =>
% 0.78/0.95       ( ![B:$i]:
% 0.78/0.95         ( ( v1_relat_1 @ B ) =>
% 0.78/0.95           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.78/0.95             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.78/0.95  thf('26', plain,
% 0.78/0.95      (![X18 : $i, X19 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X18)
% 0.78/0.95          | ((k1_relat_1 @ (k5_relat_1 @ X19 @ X18)) = (k1_relat_1 @ X19))
% 0.78/0.95          | ~ (r1_tarski @ (k2_relat_1 @ X19) @ (k1_relat_1 @ X18))
% 0.78/0.95          | ~ (v1_relat_1 @ X19))),
% 0.78/0.95      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.78/0.95  thf('27', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.78/0.95          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.78/0.95              = (k1_relat_1 @ k1_xboole_0))
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['25', '26'])).
% 0.78/0.95  thf('28', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.78/0.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.78/0.95  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.78/0.95  thf('30', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.78/0.95  thf('31', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['24', '30'])).
% 0.78/0.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.78/0.95  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('33', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0)
% 0.78/0.95          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['31', '32'])).
% 0.78/0.95  thf(fc8_relat_1, axiom,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.78/0.95       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.78/0.95  thf('34', plain,
% 0.78/0.95      (![X14 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ (k1_relat_1 @ X14))
% 0.78/0.95          | ~ (v1_relat_1 @ X14)
% 0.78/0.95          | (v1_xboole_0 @ X14))),
% 0.78/0.95      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.78/0.95  thf('35', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.78/0.95          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.78/0.95  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('37', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.78/0.95          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['35', '36'])).
% 0.78/0.95  thf('38', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0)
% 0.78/0.95          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['23', '37'])).
% 0.78/0.95  thf('39', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.78/0.95          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('simplify', [status(thm)], ['38'])).
% 0.78/0.95  thf('40', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['22', '39'])).
% 0.78/0.95  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('42', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['40', '41'])).
% 0.78/0.95  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf(l13_xboole_0, axiom,
% 0.78/0.95    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.78/0.95  thf('44', plain,
% 0.78/0.95      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.95  thf('45', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['40', '41'])).
% 0.78/0.95  thf('46', plain,
% 0.78/0.95      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.95  thf('47', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0)
% 0.78/0.95          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['45', '46'])).
% 0.78/0.95  thf('48', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.78/0.95          | ~ (v1_xboole_0 @ X0)
% 0.78/0.95          | ~ (v1_relat_1 @ X1))),
% 0.78/0.95      inference('sup+', [status(thm)], ['44', '47'])).
% 0.78/0.95  thf('49', plain,
% 0.78/0.95      (![X12 : $i, X13 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X12)
% 0.78/0.95          | ~ (v1_relat_1 @ X13)
% 0.78/0.95          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.78/0.95      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.78/0.95  thf('50', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         ((v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | ~ (v1_xboole_0 @ X1)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | ~ (v1_relat_1 @ X1))),
% 0.78/0.95      inference('sup+', [status(thm)], ['48', '49'])).
% 0.78/0.95  thf('51', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X1)
% 0.78/0.95          | ~ (v1_xboole_0 @ X1)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_relat_1 @ k1_xboole_0))),
% 0.78/0.95      inference('simplify', [status(thm)], ['50'])).
% 0.78/0.95  thf('52', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_xboole_0 @ X0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['43', '51'])).
% 0.78/0.95  thf('53', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.78/0.95      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.78/0.95  thf('54', plain,
% 0.78/0.95      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.78/0.95      inference('clc', [status(thm)], ['52', '53'])).
% 0.78/0.95  thf('55', plain,
% 0.78/0.95      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['42', '54'])).
% 0.78/0.95  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.78/0.95      inference('sup-', [status(thm)], ['21', '55'])).
% 0.78/0.95  thf('57', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('demod', [status(thm)], ['5', '20', '56'])).
% 0.78/0.95  thf(fc9_relat_1, axiom,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.78/0.95       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.78/0.95  thf('58', plain,
% 0.78/0.95      (![X15 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 0.78/0.95          | ~ (v1_relat_1 @ X15)
% 0.78/0.95          | (v1_xboole_0 @ X15))),
% 0.78/0.95      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.78/0.95  thf('59', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.78/0.95          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['57', '58'])).
% 0.78/0.95  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('61', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.78/0.95          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['59', '60'])).
% 0.78/0.95  thf('62', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ k1_xboole_0)
% 0.78/0.95          | ~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['0', '61'])).
% 0.78/0.95  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.78/0.95      inference('sup-', [status(thm)], ['21', '55'])).
% 0.78/0.95  thf('64', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0)
% 0.78/0.95          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.78/0.95          | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('demod', [status(thm)], ['62', '63'])).
% 0.78/0.95  thf('65', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.78/0.95      inference('simplify', [status(thm)], ['64'])).
% 0.78/0.95  thf('66', plain,
% 0.78/0.95      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.95  thf('67', plain,
% 0.78/0.95      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.95  thf('68', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.78/0.95      inference('sup+', [status(thm)], ['66', '67'])).
% 0.78/0.95  thf('69', plain,
% 0.78/0.95      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.95  thf('70', plain,
% 0.78/0.95      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.78/0.95        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('71', plain,
% 0.78/0.95      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.78/0.95      inference('split', [status(esa)], ['70'])).
% 0.78/0.95  thf('72', plain,
% 0.78/0.95      ((![X0 : $i]:
% 0.78/0.95          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['69', '71'])).
% 0.78/0.95  thf('73', plain,
% 0.78/0.95      ((![X0 : $i, X1 : $i]:
% 0.78/0.95          (((X0) != (k1_xboole_0))
% 0.78/0.95           | ~ (v1_xboole_0 @ X0)
% 0.78/0.95           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.78/0.95           | ~ (v1_xboole_0 @ X1)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['68', '72'])).
% 0.78/0.95  thf('74', plain,
% 0.78/0.95      ((![X1 : $i]:
% 0.78/0.95          (~ (v1_xboole_0 @ X1)
% 0.78/0.95           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.78/0.95           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.78/0.95      inference('simplify', [status(thm)], ['73'])).
% 0.78/0.95  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('76', plain,
% 0.78/0.95      ((![X1 : $i]:
% 0.78/0.95          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.78/0.95         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.78/0.95      inference('simplify_reflect+', [status(thm)], ['74', '75'])).
% 0.78/0.95  thf('77', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['40', '41'])).
% 0.78/0.95  thf('78', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.78/0.95      inference('sup+', [status(thm)], ['66', '67'])).
% 0.78/0.95  thf('79', plain,
% 0.78/0.95      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.78/0.95  thf('80', plain,
% 0.78/0.95      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.78/0.95      inference('split', [status(esa)], ['70'])).
% 0.78/0.95  thf('81', plain,
% 0.78/0.95      ((![X0 : $i]:
% 0.78/0.95          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['79', '80'])).
% 0.78/0.95  thf('82', plain,
% 0.78/0.95      ((![X0 : $i, X1 : $i]:
% 0.78/0.95          (((X0) != (k1_xboole_0))
% 0.78/0.95           | ~ (v1_xboole_0 @ X0)
% 0.78/0.95           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.78/0.95           | ~ (v1_xboole_0 @ X1)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['78', '81'])).
% 0.78/0.95  thf('83', plain,
% 0.78/0.95      ((![X1 : $i]:
% 0.78/0.95          (~ (v1_xboole_0 @ X1)
% 0.78/0.95           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.78/0.95           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.78/0.95      inference('simplify', [status(thm)], ['82'])).
% 0.78/0.95  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('85', plain,
% 0.78/0.95      ((![X1 : $i]:
% 0.78/0.95          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.78/0.95         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.78/0.95      inference('simplify_reflect+', [status(thm)], ['83', '84'])).
% 0.78/0.95  thf('86', plain,
% 0.78/0.95      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.78/0.95         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['77', '85'])).
% 0.78/0.95  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('89', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.78/0.95      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.78/0.95  thf('90', plain,
% 0.78/0.95      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.78/0.95       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.78/0.95      inference('split', [status(esa)], ['70'])).
% 0.78/0.95  thf('91', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.78/0.95      inference('sat_resolution*', [status(thm)], ['89', '90'])).
% 0.78/0.95  thf('92', plain,
% 0.78/0.95      (![X1 : $i]:
% 0.78/0.95         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1)))),
% 0.78/0.95      inference('simpl_trail', [status(thm)], ['76', '91'])).
% 0.78/0.95  thf('93', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['65', '92'])).
% 0.78/0.95  thf('94', plain, ((v1_relat_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.95  thf('96', plain, ($false),
% 0.78/0.95      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.78/0.95  
% 0.78/0.95  % SZS output end Refutation
% 0.78/0.95  
% 0.78/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
