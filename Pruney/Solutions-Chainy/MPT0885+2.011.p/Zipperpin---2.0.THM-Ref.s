%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EjVmxvlnss

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:29 EST 2020

% Result     : Theorem 4.99s
% Output     : Refutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 137 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  905 (1420 expanded)
%              Number of equality atoms :   68 ( 121 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X2 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X2 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','37'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_mcart_1 @ X36 @ X37 @ X38 )
      = ( k4_tarski @ ( k4_tarski @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('40',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_mcart_1 @ X36 @ X37 @ X38 )
      = ( k4_tarski @ ( k4_tarski @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X28 @ X31 ) @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X28 @ X29 ) @ ( k4_tarski @ X28 @ X30 ) @ ( k4_tarski @ X31 @ X29 ) @ ( k4_tarski @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_mcart_1 @ X36 @ X37 @ X38 )
      = ( k4_tarski @ ( k4_tarski @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_mcart_1 @ X36 @ X37 @ X38 )
      = ( k4_tarski @ ( k4_tarski @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_tarski @ ( k4_tarski @ X32 @ X33 ) @ ( k4_tarski @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_tarski @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X2 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k3_zfmisc_1 @ X39 @ X40 @ X41 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('53',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['38','47','50','51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EjVmxvlnss
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.99/5.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.99/5.24  % Solved by: fo/fo7.sh
% 4.99/5.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.99/5.24  % done 5616 iterations in 4.734s
% 4.99/5.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.99/5.24  % SZS output start Refutation
% 4.99/5.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.99/5.24  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 4.99/5.24  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.99/5.24  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 4.99/5.24  thf(sk_B_type, type, sk_B: $i).
% 4.99/5.24  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.99/5.24  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.99/5.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.99/5.24  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.99/5.24  thf(sk_C_type, type, sk_C: $i).
% 4.99/5.24  thf(sk_D_type, type, sk_D: $i).
% 4.99/5.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.99/5.24  thf(sk_E_type, type, sk_E: $i).
% 4.99/5.24  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.99/5.24  thf(sk_A_type, type, sk_A: $i).
% 4.99/5.24  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.99/5.24  thf(t45_mcart_1, conjecture,
% 4.99/5.24    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.99/5.24     ( ( k3_zfmisc_1 @
% 4.99/5.24         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 4.99/5.24       ( k2_enumset1 @
% 4.99/5.24         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 4.99/5.24         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 4.99/5.24  thf(zf_stmt_0, negated_conjecture,
% 4.99/5.24    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.99/5.24        ( ( k3_zfmisc_1 @
% 4.99/5.24            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 4.99/5.24          ( k2_enumset1 @
% 4.99/5.24            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 4.99/5.24            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 4.99/5.24    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 4.99/5.24  thf('0', plain,
% 4.99/5.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 4.99/5.24         (k2_tarski @ sk_D @ sk_E))
% 4.99/5.24         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 4.99/5.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 4.99/5.24             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 4.99/5.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 4.99/5.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.99/5.24  thf(t70_enumset1, axiom,
% 4.99/5.24    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.99/5.24  thf('1', plain,
% 4.99/5.24      (![X12 : $i, X13 : $i]:
% 4.99/5.24         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 4.99/5.24      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.99/5.24  thf(commutativity_k2_tarski, axiom,
% 4.99/5.24    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.99/5.24  thf('2', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.99/5.24      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.99/5.24  thf('3', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]:
% 4.99/5.24         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 4.99/5.24      inference('sup+', [status(thm)], ['1', '2'])).
% 4.99/5.24  thf('4', plain,
% 4.99/5.24      (![X12 : $i, X13 : $i]:
% 4.99/5.24         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 4.99/5.24      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.99/5.24  thf('5', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]:
% 4.99/5.24         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 4.99/5.24      inference('sup+', [status(thm)], ['3', '4'])).
% 4.99/5.24  thf(t44_enumset1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i,D:$i]:
% 4.99/5.24     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 4.99/5.24       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 4.99/5.24  thf('6', plain,
% 4.99/5.24      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 4.99/5.24           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X3 @ X4 @ X5)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t44_enumset1])).
% 4.99/5.24  thf('7', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X2 @ X0 @ X0 @ X1)
% 4.99/5.24           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X1 @ X1 @ X0)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['5', '6'])).
% 4.99/5.24  thf('8', plain,
% 4.99/5.24      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 4.99/5.24           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X3 @ X4 @ X5)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t44_enumset1])).
% 4.99/5.24  thf('9', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X2 @ X0 @ X0 @ X1) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 4.99/5.24      inference('demod', [status(thm)], ['7', '8'])).
% 4.99/5.24  thf(t71_enumset1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i]:
% 4.99/5.24     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.99/5.24  thf('10', plain,
% 4.99/5.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 4.99/5.24           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 4.99/5.24      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.99/5.24  thf(t50_enumset1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.99/5.24     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 4.99/5.24       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 4.99/5.24  thf('11', plain,
% 4.99/5.24      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 4.99/5.24           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 4.99/5.24              (k1_tarski @ X10)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t50_enumset1])).
% 4.99/5.24  thf('12', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 4.99/5.24           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['10', '11'])).
% 4.99/5.24  thf('13', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.99/5.24      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.99/5.24  thf(l51_zfmisc_1, axiom,
% 4.99/5.24    (![A:$i,B:$i]:
% 4.99/5.24     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.99/5.24  thf('14', plain,
% 4.99/5.24      (![X26 : $i, X27 : $i]:
% 4.99/5.24         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 4.99/5.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.99/5.24  thf('15', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]:
% 4.99/5.24         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.99/5.24      inference('sup+', [status(thm)], ['13', '14'])).
% 4.99/5.24  thf('16', plain,
% 4.99/5.24      (![X26 : $i, X27 : $i]:
% 4.99/5.24         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 4.99/5.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.99/5.24  thf('17', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.99/5.24      inference('sup+', [status(thm)], ['15', '16'])).
% 4.99/5.24  thf('18', plain,
% 4.99/5.24      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 4.99/5.24           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X3 @ X4 @ X5)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t44_enumset1])).
% 4.99/5.24  thf('19', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 4.99/5.24           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['17', '18'])).
% 4.99/5.24  thf('20', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 4.99/5.24           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.99/5.24      inference('demod', [status(thm)], ['12', '19'])).
% 4.99/5.24  thf('21', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2)
% 4.99/5.24           = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 4.99/5.24      inference('sup+', [status(thm)], ['9', '20'])).
% 4.99/5.24  thf(t72_enumset1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i,D:$i]:
% 4.99/5.24     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.99/5.24  thf('22', plain,
% 4.99/5.24      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 4.99/5.24           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 4.99/5.24      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.99/5.24  thf('23', plain,
% 4.99/5.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 4.99/5.24           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 4.99/5.24      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.99/5.24  thf('24', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.99/5.24      inference('sup+', [status(thm)], ['22', '23'])).
% 4.99/5.24  thf('25', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 4.99/5.24      inference('demod', [status(thm)], ['21', '24'])).
% 4.99/5.24  thf('26', plain,
% 4.99/5.24      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 4.99/5.24           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 4.99/5.24              (k1_tarski @ X10)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t50_enumset1])).
% 4.99/5.24  thf('27', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X0 @ X1 @ X1 @ X2 @ X3)
% 4.99/5.24           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['25', '26'])).
% 4.99/5.24  thf('28', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 4.99/5.24           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['17', '18'])).
% 4.99/5.24  thf('29', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X0 @ X1 @ X1 @ X2 @ X3)
% 4.99/5.24           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.99/5.24      inference('demod', [status(thm)], ['27', '28'])).
% 4.99/5.24  thf('30', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 4.99/5.24           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.99/5.24      inference('demod', [status(thm)], ['12', '19'])).
% 4.99/5.24  thf('31', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.99/5.24      inference('sup+', [status(thm)], ['22', '23'])).
% 4.99/5.24  thf('32', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 4.99/5.24      inference('sup+', [status(thm)], ['30', '31'])).
% 4.99/5.24  thf('33', plain,
% 4.99/5.24      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 4.99/5.24           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 4.99/5.24              (k1_tarski @ X10)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t50_enumset1])).
% 4.99/5.24  thf('34', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X0 @ X2 @ X2 @ X1 @ X3)
% 4.99/5.24           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['32', '33'])).
% 4.99/5.24  thf('35', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 4.99/5.24           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['17', '18'])).
% 4.99/5.24  thf('36', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k3_enumset1 @ X0 @ X2 @ X2 @ X1 @ X3)
% 4.99/5.24           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.99/5.24      inference('demod', [status(thm)], ['34', '35'])).
% 4.99/5.24  thf('37', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.99/5.24         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 4.99/5.24      inference('sup+', [status(thm)], ['29', '36'])).
% 4.99/5.24  thf('38', plain,
% 4.99/5.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 4.99/5.24         (k2_tarski @ sk_D @ sk_E))
% 4.99/5.24         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 4.99/5.24             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 4.99/5.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 4.99/5.24             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 4.99/5.24      inference('demod', [status(thm)], ['0', '37'])).
% 4.99/5.24  thf(d3_mcart_1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i]:
% 4.99/5.24     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 4.99/5.24  thf('39', plain,
% 4.99/5.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.99/5.24         ((k3_mcart_1 @ X36 @ X37 @ X38)
% 4.99/5.24           = (k4_tarski @ (k4_tarski @ X36 @ X37) @ X38))),
% 4.99/5.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.99/5.24  thf('40', plain,
% 4.99/5.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.99/5.24         ((k3_mcart_1 @ X36 @ X37 @ X38)
% 4.99/5.24           = (k4_tarski @ (k4_tarski @ X36 @ X37) @ X38))),
% 4.99/5.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.99/5.24  thf(t146_zfmisc_1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i,D:$i]:
% 4.99/5.24     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 4.99/5.24       ( k2_enumset1 @
% 4.99/5.24         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 4.99/5.24         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 4.99/5.24  thf('41', plain,
% 4.99/5.24      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.99/5.24         ((k2_zfmisc_1 @ (k2_tarski @ X28 @ X31) @ (k2_tarski @ X29 @ X30))
% 4.99/5.24           = (k2_enumset1 @ (k4_tarski @ X28 @ X29) @ 
% 4.99/5.24              (k4_tarski @ X28 @ X30) @ (k4_tarski @ X31 @ X29) @ 
% 4.99/5.24              (k4_tarski @ X31 @ X30)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 4.99/5.24  thf('42', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.99/5.24         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 4.99/5.24           (k2_tarski @ X0 @ X3))
% 4.99/5.24           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 4.99/5.24              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 4.99/5.24              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['40', '41'])).
% 4.99/5.24  thf('43', plain,
% 4.99/5.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.99/5.24         ((k3_mcart_1 @ X36 @ X37 @ X38)
% 4.99/5.24           = (k4_tarski @ (k4_tarski @ X36 @ X37) @ X38))),
% 4.99/5.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.99/5.24  thf('44', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.99/5.24         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 4.99/5.24           (k2_tarski @ X0 @ X3))
% 4.99/5.24           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 4.99/5.24              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 4.99/5.24              (k4_tarski @ X4 @ X3)))),
% 4.99/5.24      inference('demod', [status(thm)], ['42', '43'])).
% 4.99/5.24  thf('45', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.99/5.24         ((k2_zfmisc_1 @ 
% 4.99/5.24           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 4.99/5.24           (k2_tarski @ X0 @ X3))
% 4.99/5.24           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 4.99/5.24              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 4.99/5.24              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['39', '44'])).
% 4.99/5.24  thf('46', plain,
% 4.99/5.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.99/5.24         ((k3_mcart_1 @ X36 @ X37 @ X38)
% 4.99/5.24           = (k4_tarski @ (k4_tarski @ X36 @ X37) @ X38))),
% 4.99/5.24      inference('cnf', [status(esa)], [d3_mcart_1])).
% 4.99/5.24  thf('47', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.99/5.24         ((k2_zfmisc_1 @ 
% 4.99/5.24           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 4.99/5.24           (k2_tarski @ X0 @ X3))
% 4.99/5.24           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 4.99/5.24              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 4.99/5.24              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 4.99/5.24      inference('demod', [status(thm)], ['45', '46'])).
% 4.99/5.24  thf(t36_zfmisc_1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i]:
% 4.99/5.24     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 4.99/5.24         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 4.99/5.24       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 4.99/5.24         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 4.99/5.24  thf('48', plain,
% 4.99/5.24      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.99/5.24         ((k2_zfmisc_1 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34))
% 4.99/5.24           = (k2_tarski @ (k4_tarski @ X32 @ X33) @ (k4_tarski @ X32 @ X34)))),
% 4.99/5.24      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 4.99/5.24  thf('49', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.99/5.24      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.99/5.24  thf('50', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.99/5.24         ((k2_tarski @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X2 @ X1))
% 4.99/5.24           = (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 4.99/5.24      inference('sup+', [status(thm)], ['48', '49'])).
% 4.99/5.24  thf('51', plain,
% 4.99/5.24      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 4.99/5.24      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.99/5.24  thf(d3_zfmisc_1, axiom,
% 4.99/5.24    (![A:$i,B:$i,C:$i]:
% 4.99/5.24     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 4.99/5.24       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 4.99/5.24  thf('52', plain,
% 4.99/5.24      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.99/5.24         ((k3_zfmisc_1 @ X39 @ X40 @ X41)
% 4.99/5.24           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40) @ X41))),
% 4.99/5.24      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 4.99/5.24  thf('53', plain,
% 4.99/5.24      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 4.99/5.24         (k2_tarski @ sk_D @ sk_E))
% 4.99/5.24         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 4.99/5.24             (k2_tarski @ sk_D @ sk_E)))),
% 4.99/5.24      inference('demod', [status(thm)], ['38', '47', '50', '51', '52'])).
% 4.99/5.24  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 4.99/5.24  
% 4.99/5.24  % SZS output end Refutation
% 4.99/5.24  
% 4.99/5.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
