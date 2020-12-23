%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NHLPyswYtm

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:18 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 203 expanded)
%              Number of leaves         :   31 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  642 (1333 expanded)
%              Number of equality atoms :   63 ( 128 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( r1_tarski @ ( k1_tarski @ X60 ) @ ( k2_tarski @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('40',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('41',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','41'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('51',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','67'])).

thf('69',plain,(
    ( k2_tarski @ sk_A @ sk_B_1 )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','68'])).

thf('70',plain,(
    $false ),
    inference(simplify,[status(thm)],['69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NHLPyswYtm
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.28/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.28/1.49  % Solved by: fo/fo7.sh
% 1.28/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.49  % done 3598 iterations in 1.041s
% 1.28/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.28/1.49  % SZS output start Refutation
% 1.28/1.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.28/1.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.28/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.28/1.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.28/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.28/1.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.28/1.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.28/1.49  thf(sk_B_type, type, sk_B: $i > $i).
% 1.28/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.28/1.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.28/1.49  thf(t14_zfmisc_1, conjecture,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.28/1.49       ( k2_tarski @ A @ B ) ))).
% 1.28/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.49    (~( ![A:$i,B:$i]:
% 1.28/1.49        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.28/1.49          ( k2_tarski @ A @ B ) ) )),
% 1.28/1.49    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 1.28/1.49  thf('0', plain,
% 1.28/1.49      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B_1))
% 1.28/1.49         != (k2_tarski @ sk_A @ sk_B_1))),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf(t12_zfmisc_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.28/1.49  thf('1', plain,
% 1.28/1.49      (![X60 : $i, X61 : $i]:
% 1.28/1.49         (r1_tarski @ (k1_tarski @ X60) @ (k2_tarski @ X60 @ X61))),
% 1.28/1.49      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.28/1.49  thf(t28_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.28/1.49  thf('2', plain,
% 1.28/1.49      (![X16 : $i, X17 : $i]:
% 1.28/1.49         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.28/1.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.28/1.49  thf('3', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.28/1.49           = (k1_tarski @ X1))),
% 1.28/1.49      inference('sup-', [status(thm)], ['1', '2'])).
% 1.28/1.49  thf(commutativity_k3_xboole_0, axiom,
% 1.28/1.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.28/1.49  thf('4', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.28/1.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.28/1.49  thf(t36_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.28/1.49  thf('5', plain,
% 1.28/1.49      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 1.28/1.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.28/1.49  thf('6', plain,
% 1.28/1.49      (![X16 : $i, X17 : $i]:
% 1.28/1.49         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.28/1.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.28/1.49  thf('7', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.28/1.49           = (k4_xboole_0 @ X0 @ X1))),
% 1.28/1.49      inference('sup-', [status(thm)], ['5', '6'])).
% 1.28/1.49  thf('8', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.28/1.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.28/1.49  thf('9', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.28/1.49           = (k4_xboole_0 @ X0 @ X1))),
% 1.28/1.49      inference('demod', [status(thm)], ['7', '8'])).
% 1.28/1.49  thf(t100_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.28/1.49  thf('10', plain,
% 1.28/1.49      (![X14 : $i, X15 : $i]:
% 1.28/1.49         ((k4_xboole_0 @ X14 @ X15)
% 1.28/1.49           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.28/1.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.28/1.49  thf('11', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.28/1.49           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.28/1.49      inference('sup+', [status(thm)], ['9', '10'])).
% 1.28/1.49  thf('12', plain,
% 1.28/1.49      (![X14 : $i, X15 : $i]:
% 1.28/1.49         ((k4_xboole_0 @ X14 @ X15)
% 1.28/1.49           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.28/1.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.28/1.49  thf(d10_xboole_0, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.28/1.49  thf('13', plain,
% 1.28/1.49      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 1.28/1.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.28/1.49  thf('14', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 1.28/1.49      inference('simplify', [status(thm)], ['13'])).
% 1.28/1.49  thf('15', plain,
% 1.28/1.49      (![X16 : $i, X17 : $i]:
% 1.28/1.49         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.28/1.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.28/1.49  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.28/1.49      inference('sup-', [status(thm)], ['14', '15'])).
% 1.28/1.49  thf('17', plain,
% 1.28/1.49      (![X14 : $i, X15 : $i]:
% 1.28/1.49         ((k4_xboole_0 @ X14 @ X15)
% 1.28/1.49           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.28/1.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.28/1.49  thf('18', plain,
% 1.28/1.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.28/1.49      inference('sup+', [status(thm)], ['16', '17'])).
% 1.28/1.49  thf(t91_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i,C:$i]:
% 1.28/1.49     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.28/1.49       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.28/1.49  thf('19', plain,
% 1.28/1.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.28/1.49         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 1.28/1.49           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 1.28/1.49      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.28/1.49  thf(commutativity_k5_xboole_0, axiom,
% 1.28/1.49    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.28/1.49  thf('20', plain,
% 1.28/1.49      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.28/1.49      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.28/1.49  thf('21', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.49         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.28/1.49           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.28/1.49      inference('sup+', [status(thm)], ['19', '20'])).
% 1.28/1.49  thf('22', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 1.28/1.49           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.28/1.49      inference('sup+', [status(thm)], ['18', '21'])).
% 1.28/1.49  thf('23', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.28/1.49           = (k4_xboole_0 @ X0 @ X1))),
% 1.28/1.49      inference('demod', [status(thm)], ['7', '8'])).
% 1.28/1.49  thf(t79_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.28/1.49  thf('24', plain,
% 1.28/1.49      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 1.28/1.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.28/1.49  thf(d1_xboole_0, axiom,
% 1.28/1.49    (![A:$i]:
% 1.28/1.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.28/1.49  thf('25', plain,
% 1.28/1.49      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.28/1.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.28/1.49  thf(t4_xboole_0, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.28/1.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.28/1.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.28/1.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.28/1.49  thf('26', plain,
% 1.28/1.49      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.28/1.49         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 1.28/1.49          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.28/1.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.28/1.49  thf('27', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.28/1.49      inference('sup-', [status(thm)], ['25', '26'])).
% 1.28/1.49  thf('28', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         (v1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.28/1.49      inference('sup-', [status(thm)], ['24', '27'])).
% 1.28/1.49  thf('29', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.28/1.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.28/1.49  thf('30', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         (v1_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.28/1.49      inference('demod', [status(thm)], ['28', '29'])).
% 1.28/1.49  thf('31', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.28/1.50      inference('sup+', [status(thm)], ['23', '30'])).
% 1.28/1.50  thf('32', plain,
% 1.28/1.50      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.28/1.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.28/1.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.28/1.50  thf('33', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 1.28/1.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.28/1.50  thf('34', plain,
% 1.28/1.50      (![X16 : $i, X17 : $i]:
% 1.28/1.50         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.28/1.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.28/1.50  thf('35', plain,
% 1.28/1.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.28/1.50      inference('sup-', [status(thm)], ['33', '34'])).
% 1.28/1.50  thf('36', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.28/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.28/1.50  thf('37', plain,
% 1.28/1.50      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.28/1.50         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 1.28/1.50          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.28/1.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.28/1.50  thf('38', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.28/1.50          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.28/1.50      inference('sup-', [status(thm)], ['36', '37'])).
% 1.28/1.50  thf('39', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.28/1.50      inference('sup-', [status(thm)], ['35', '38'])).
% 1.28/1.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.28/1.50  thf('40', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 1.28/1.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.28/1.50  thf('41', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.28/1.50      inference('demod', [status(thm)], ['39', '40'])).
% 1.28/1.50  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.50      inference('sup-', [status(thm)], ['32', '41'])).
% 1.28/1.50  thf(t8_boole, axiom,
% 1.28/1.50    (![A:$i,B:$i]:
% 1.28/1.50     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.28/1.50  thf('43', plain,
% 1.28/1.50      (![X25 : $i, X26 : $i]:
% 1.28/1.50         (~ (v1_xboole_0 @ X25) | ~ (v1_xboole_0 @ X26) | ((X25) = (X26)))),
% 1.28/1.50      inference('cnf', [status(esa)], [t8_boole])).
% 1.28/1.50  thf('44', plain,
% 1.28/1.50      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.28/1.50      inference('sup-', [status(thm)], ['42', '43'])).
% 1.28/1.50  thf('45', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.28/1.50      inference('sup-', [status(thm)], ['31', '44'])).
% 1.28/1.50  thf('46', plain,
% 1.28/1.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.28/1.50      inference('sup-', [status(thm)], ['33', '34'])).
% 1.28/1.50  thf('47', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.28/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.28/1.50  thf('48', plain,
% 1.28/1.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.50      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.50  thf('49', plain,
% 1.28/1.50      (![X14 : $i, X15 : $i]:
% 1.28/1.50         ((k4_xboole_0 @ X14 @ X15)
% 1.28/1.50           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.28/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.28/1.50  thf('50', plain,
% 1.28/1.50      (![X0 : $i]:
% 1.28/1.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.28/1.50      inference('sup+', [status(thm)], ['48', '49'])).
% 1.28/1.50  thf(t3_boole, axiom,
% 1.28/1.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.28/1.50  thf('51', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.28/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.28/1.50  thf('52', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.28/1.50      inference('demod', [status(thm)], ['50', '51'])).
% 1.28/1.50  thf('53', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['45', '52'])).
% 1.28/1.50  thf('54', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.28/1.50      inference('demod', [status(thm)], ['22', '53'])).
% 1.28/1.50  thf('55', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k3_xboole_0 @ X1 @ X0)
% 1.28/1.50           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['12', '54'])).
% 1.28/1.50  thf('56', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k3_xboole_0 @ X1 @ X0)
% 1.28/1.50           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['11', '55'])).
% 1.28/1.50  thf('57', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.28/1.50           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['9', '10'])).
% 1.28/1.50  thf('58', plain,
% 1.28/1.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.28/1.50      inference('sup+', [status(thm)], ['16', '17'])).
% 1.28/1.50  thf('59', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.50         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.28/1.50           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['19', '20'])).
% 1.28/1.50  thf('60', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.28/1.50           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['58', '59'])).
% 1.28/1.50  thf('61', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.28/1.50      inference('sup+', [status(thm)], ['45', '52'])).
% 1.28/1.50  thf('62', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.28/1.50      inference('demod', [status(thm)], ['60', '61'])).
% 1.28/1.50  thf('63', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.28/1.50           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 1.28/1.50      inference('sup+', [status(thm)], ['57', '62'])).
% 1.28/1.50  thf(t98_xboole_1, axiom,
% 1.28/1.50    (![A:$i,B:$i]:
% 1.28/1.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.28/1.50  thf('64', plain,
% 1.28/1.50      (![X30 : $i, X31 : $i]:
% 1.28/1.50         ((k2_xboole_0 @ X30 @ X31)
% 1.28/1.50           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 1.28/1.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.28/1.50  thf('65', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.28/1.50      inference('demod', [status(thm)], ['63', '64'])).
% 1.28/1.50  thf('66', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.28/1.50      inference('sup+', [status(thm)], ['56', '65'])).
% 1.28/1.50  thf('67', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 1.28/1.50      inference('sup+', [status(thm)], ['4', '66'])).
% 1.28/1.50  thf('68', plain,
% 1.28/1.50      (![X0 : $i, X1 : $i]:
% 1.28/1.50         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 1.28/1.50           = (k2_tarski @ X0 @ X1))),
% 1.28/1.50      inference('sup+', [status(thm)], ['3', '67'])).
% 1.28/1.50  thf('69', plain,
% 1.28/1.50      (((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))),
% 1.28/1.50      inference('demod', [status(thm)], ['0', '68'])).
% 1.28/1.50  thf('70', plain, ($false), inference('simplify', [status(thm)], ['69'])).
% 1.28/1.50  
% 1.28/1.50  % SZS output end Refutation
% 1.28/1.50  
% 1.36/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
