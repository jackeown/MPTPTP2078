%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E3a3bjoAct

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:04 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 170 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   21
%              Number of atoms          :  754 (1367 expanded)
%              Number of equality atoms :   75 ( 153 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X32 @ X34 ) @ X35 )
        = ( k2_tarski @ X32 @ X34 ) )
      | ( r2_hidden @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ X2 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) @ X2 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_zfmisc_1 @ X26 @ X27 )
        = k1_xboole_0 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ X26 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X28 @ X30 ) @ X29 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ X26 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ X26 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','47'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['13','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['9','66'])).

thf('68',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E3a3bjoAct
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.15  % Solved by: fo/fo7.sh
% 0.89/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.15  % done 1976 iterations in 0.692s
% 0.89/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.15  % SZS output start Refutation
% 0.89/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.15  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.15  thf(t144_zfmisc_1, conjecture,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.89/1.15          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.89/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.15    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.15        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.89/1.15             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.89/1.15    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.89/1.15  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.89/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.15  thf(t72_zfmisc_1, axiom,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.89/1.15       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.89/1.15  thf('1', plain,
% 0.89/1.15      (![X32 : $i, X34 : $i, X35 : $i]:
% 0.89/1.15         (((k4_xboole_0 @ (k2_tarski @ X32 @ X34) @ X35)
% 0.89/1.15            = (k2_tarski @ X32 @ X34))
% 0.89/1.15          | (r2_hidden @ X34 @ X35)
% 0.89/1.15          | (r2_hidden @ X32 @ X35))),
% 0.89/1.15      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.89/1.15  thf(t40_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('2', plain,
% 0.89/1.15      (![X9 : $i, X10 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.89/1.15           = (k4_xboole_0 @ X9 @ X10))),
% 0.89/1.15      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.89/1.15  thf(t48_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('3', plain,
% 0.89/1.15      (![X16 : $i, X17 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.89/1.15           = (k3_xboole_0 @ X16 @ X17))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('4', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.15  thf('5', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         (((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) @ 
% 0.89/1.15            (k2_tarski @ X1 @ X0))
% 0.89/1.15            = (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) @ X2))
% 0.89/1.15          | (r2_hidden @ X1 @ X2)
% 0.89/1.15          | (r2_hidden @ X0 @ X2))),
% 0.89/1.15      inference('sup+', [status(thm)], ['1', '4'])).
% 0.89/1.15  thf(commutativity_k2_xboole_0, axiom,
% 0.89/1.15    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.89/1.15  thf('6', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('7', plain,
% 0.89/1.15      (![X9 : $i, X10 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.89/1.15           = (k4_xboole_0 @ X9 @ X10))),
% 0.89/1.15      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.89/1.15  thf('8', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.89/1.15           = (k4_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.15  thf('9', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0))
% 0.89/1.15            = (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) @ X2))
% 0.89/1.15          | (r2_hidden @ X1 @ X2)
% 0.89/1.15          | (r2_hidden @ X0 @ X2))),
% 0.89/1.15      inference('demod', [status(thm)], ['5', '8'])).
% 0.89/1.15  thf('10', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf(t39_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('11', plain,
% 0.89/1.15      (![X7 : $i, X8 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.89/1.15           = (k2_xboole_0 @ X7 @ X8))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('12', plain,
% 0.89/1.15      (![X9 : $i, X10 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.89/1.15           = (k4_xboole_0 @ X9 @ X10))),
% 0.89/1.15      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.89/1.15  thf('13', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.89/1.15           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['11', '12'])).
% 0.89/1.15  thf('14', plain,
% 0.89/1.15      (![X16 : $i, X17 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.89/1.15           = (k3_xboole_0 @ X16 @ X17))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('15', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf(t7_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('16', plain,
% 0.89/1.15      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.89/1.15      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.89/1.15  thf('17', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['15', '16'])).
% 0.89/1.15  thf(t43_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.89/1.15       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.89/1.15  thf('18', plain,
% 0.89/1.15      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.89/1.15         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.89/1.15          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.89/1.15  thf('19', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.89/1.15      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.15  thf(t12_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.89/1.15  thf('20', plain,
% 0.89/1.15      (![X5 : $i, X6 : $i]:
% 0.89/1.15         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.89/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.15  thf('21', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.15  thf('22', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('23', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.89/1.15      inference('demod', [status(thm)], ['21', '22'])).
% 0.89/1.15  thf('24', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.15  thf('25', plain,
% 0.89/1.15      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.89/1.15      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.89/1.15  thf('26', plain,
% 0.89/1.15      (![X5 : $i, X6 : $i]:
% 0.89/1.15         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.89/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.15  thf('27', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (k2_xboole_0 @ X1 @ X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['25', '26'])).
% 0.89/1.15  thf('28', plain,
% 0.89/1.15      (![X9 : $i, X10 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.89/1.15           = (k4_xboole_0 @ X9 @ X10))),
% 0.89/1.15      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.89/1.15  thf('29', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['27', '28'])).
% 0.89/1.15  thf('30', plain,
% 0.89/1.15      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 0.89/1.15      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.89/1.15  thf('31', plain,
% 0.89/1.15      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.89/1.15         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.89/1.15          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.89/1.15  thf('32', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.89/1.15      inference('sup-', [status(thm)], ['30', '31'])).
% 0.89/1.15  thf(t113_zfmisc_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.89/1.15       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.15  thf('33', plain,
% 0.89/1.15      (![X26 : $i, X27 : $i]:
% 0.89/1.15         (((k2_zfmisc_1 @ X26 @ X27) = (k1_xboole_0))
% 0.89/1.15          | ((X27) != (k1_xboole_0)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.89/1.15  thf('34', plain,
% 0.89/1.15      (![X26 : $i]: ((k2_zfmisc_1 @ X26 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.15      inference('simplify', [status(thm)], ['33'])).
% 0.89/1.15  thf(t125_zfmisc_1, axiom,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.89/1.15         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.89/1.15       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.89/1.15         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.89/1.15  thf('35', plain,
% 0.89/1.15      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.15         ((k2_zfmisc_1 @ (k4_xboole_0 @ X28 @ X30) @ X29)
% 0.89/1.15           = (k4_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ 
% 0.89/1.15              (k2_zfmisc_1 @ X30 @ X29)))),
% 0.89/1.15      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.89/1.15  thf('36', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.89/1.15           = (k4_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['34', '35'])).
% 0.89/1.15  thf('37', plain,
% 0.89/1.15      (![X26 : $i]: ((k2_zfmisc_1 @ X26 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.15      inference('simplify', [status(thm)], ['33'])).
% 0.89/1.15  thf('38', plain,
% 0.89/1.15      (![X26 : $i]: ((k2_zfmisc_1 @ X26 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.15      inference('simplify', [status(thm)], ['33'])).
% 0.89/1.15  thf('39', plain,
% 0.89/1.15      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.89/1.15  thf('40', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.89/1.15      inference('sup-', [status(thm)], ['30', '31'])).
% 0.89/1.15  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.89/1.15      inference('sup+', [status(thm)], ['39', '40'])).
% 0.89/1.15  thf(d10_xboole_0, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.15  thf('42', plain,
% 0.89/1.15      (![X2 : $i, X4 : $i]:
% 0.89/1.15         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.89/1.15      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.15  thf('43', plain,
% 0.89/1.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.89/1.15      inference('sup-', [status(thm)], ['41', '42'])).
% 0.89/1.15  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['32', '43'])).
% 0.89/1.15  thf('45', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('demod', [status(thm)], ['29', '44'])).
% 0.89/1.15  thf('46', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['24', '45'])).
% 0.89/1.15  thf('47', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['23', '46'])).
% 0.89/1.15  thf('48', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['14', '47'])).
% 0.89/1.15  thf(t49_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i,C:$i]:
% 0.89/1.15     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.89/1.15       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.89/1.15  thf('49', plain,
% 0.89/1.15      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.15         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.15           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.89/1.15      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.89/1.15  thf(t47_xboole_1, axiom,
% 0.89/1.15    (![A:$i,B:$i]:
% 0.89/1.15     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.89/1.15  thf('50', plain,
% 0.89/1.15      (![X14 : $i, X15 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.89/1.15           = (k4_xboole_0 @ X14 @ X15))),
% 0.89/1.15      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.89/1.15  thf('51', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.89/1.15           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['49', '50'])).
% 0.89/1.15  thf('52', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.89/1.15           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('sup+', [status(thm)], ['48', '51'])).
% 0.89/1.15  thf('53', plain,
% 0.89/1.15      (![X7 : $i, X8 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.89/1.15           = (k2_xboole_0 @ X7 @ X8))),
% 0.89/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.15  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.89/1.15      inference('sup+', [status(thm)], ['39', '40'])).
% 0.89/1.15  thf('55', plain,
% 0.89/1.15      (![X5 : $i, X6 : $i]:
% 0.89/1.15         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.89/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.15  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.15  thf('57', plain,
% 0.89/1.15      (![X0 : $i]:
% 0.89/1.15         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['53', '56'])).
% 0.89/1.15  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.15      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.15  thf('59', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.15      inference('demod', [status(thm)], ['57', '58'])).
% 0.89/1.15  thf('60', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.15      inference('demod', [status(thm)], ['52', '59'])).
% 0.89/1.15  thf('61', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.89/1.15           = (X1))),
% 0.89/1.15      inference('demod', [status(thm)], ['13', '60'])).
% 0.89/1.15  thf('62', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.89/1.15           = (k4_xboole_0 @ X0 @ X1))),
% 0.89/1.15      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.15  thf('63', plain,
% 0.89/1.15      (![X16 : $i, X17 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.89/1.15           = (k3_xboole_0 @ X16 @ X17))),
% 0.89/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.15  thf('64', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.89/1.15           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['62', '63'])).
% 0.89/1.15  thf('65', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['61', '64'])).
% 0.89/1.15  thf('66', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i]:
% 0.89/1.15         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.89/1.15      inference('sup+', [status(thm)], ['10', '65'])).
% 0.89/1.15  thf('67', plain,
% 0.89/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.15         (((k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) = (X2))
% 0.89/1.15          | (r2_hidden @ X1 @ X2)
% 0.89/1.15          | (r2_hidden @ X0 @ X2))),
% 0.89/1.15      inference('demod', [status(thm)], ['9', '66'])).
% 0.89/1.15  thf('68', plain,
% 0.89/1.15      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.89/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.15  thf('69', plain,
% 0.89/1.15      ((((sk_C) != (sk_C))
% 0.89/1.15        | (r2_hidden @ sk_B @ sk_C)
% 0.89/1.15        | (r2_hidden @ sk_A @ sk_C))),
% 0.89/1.15      inference('sup-', [status(thm)], ['67', '68'])).
% 0.89/1.15  thf('70', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.89/1.15      inference('simplify', [status(thm)], ['69'])).
% 0.89/1.15  thf('71', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.89/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.15  thf('72', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.89/1.15      inference('clc', [status(thm)], ['70', '71'])).
% 0.89/1.15  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.89/1.15  
% 0.89/1.15  % SZS output end Refutation
% 0.89/1.15  
% 0.89/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
