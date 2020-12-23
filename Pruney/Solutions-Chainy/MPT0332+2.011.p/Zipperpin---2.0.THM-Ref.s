%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oHErcOlIbH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:08 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  106 (1650 expanded)
%              Number of leaves         :   20 ( 562 expanded)
%              Depth                    :   23
%              Number of atoms          :  797 (12339 expanded)
%              Number of equality atoms :   91 (1635 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ( r2_hidden @ X26 @ X25 )
      | ( X25
        = ( k4_xboole_0 @ X25 @ ( k2_tarski @ X24 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','51'])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','51'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','77'])).

thf('79',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','78'])).

thf('80',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oHErcOlIbH
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.77  % Solved by: fo/fo7.sh
% 0.60/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.77  % done 647 iterations in 0.319s
% 0.60/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.77  % SZS output start Refutation
% 0.60/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(t145_zfmisc_1, conjecture,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.60/0.77          ( ( C ) !=
% 0.60/0.77            ( k4_xboole_0 @
% 0.60/0.77              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.60/0.77              ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.77        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.60/0.77             ( ( C ) !=
% 0.60/0.77               ( k4_xboole_0 @
% 0.60/0.77                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.60/0.77                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 0.60/0.77  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(t144_zfmisc_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.60/0.77          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.60/0.77  thf('1', plain,
% 0.60/0.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.77         ((r2_hidden @ X24 @ X25)
% 0.60/0.77          | (r2_hidden @ X26 @ X25)
% 0.60/0.77          | ((X25) = (k4_xboole_0 @ X25 @ (k2_tarski @ X24 @ X26))))),
% 0.60/0.77      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.60/0.77  thf('2', plain,
% 0.60/0.77      (((sk_C)
% 0.60/0.77         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.60/0.77             (k2_tarski @ sk_A @ sk_B)))),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.77  thf('3', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.77  thf('4', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.77  thf(t21_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X4 : $i, X5 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.60/0.77      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['4', '5'])).
% 0.60/0.77  thf(t100_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.77           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.77  thf('8', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k5_xboole_0 @ X0 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['6', '7'])).
% 0.60/0.77  thf(t92_xboole_1, axiom,
% 0.60/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.60/0.77  thf('9', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['8', '9'])).
% 0.60/0.77  thf(t98_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.60/0.77  thf('11', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X13 @ X14)
% 0.60/0.77           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.60/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['10', '11'])).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.77  thf(t2_boole, axiom,
% 0.60/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.60/0.77  thf('14', plain,
% 0.60/0.77      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.77           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.77  thf('16', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.60/0.77  thf('17', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.60/0.77  thf('18', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.60/0.77  thf('19', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.60/0.77  thf(t91_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.60/0.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.60/0.77  thf('20', plain,
% 0.60/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.60/0.77           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.60/0.77  thf('21', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['19', '20'])).
% 0.60/0.77  thf('22', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['18', '21'])).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.60/0.77  thf('24', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['19', '20'])).
% 0.60/0.77  thf('26', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.60/0.77  thf('27', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.77  thf('28', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.60/0.77           = (k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['24', '27'])).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.60/0.77  thf('30', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.60/0.77           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.60/0.77  thf('31', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['22', '23'])).
% 0.60/0.77  thf('32', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X13 @ X14)
% 0.60/0.77           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.77  thf('33', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.60/0.77           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['31', '32'])).
% 0.60/0.77  thf('34', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['30', '33'])).
% 0.60/0.77  thf('35', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.60/0.77  thf('36', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.60/0.77           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['34', '35'])).
% 0.60/0.77  thf('37', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['30', '33'])).
% 0.60/0.77  thf('38', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.60/0.77           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['28', '29'])).
% 0.60/0.77  thf('39', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.60/0.77           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.60/0.77  thf(t95_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( k3_xboole_0 @ A @ B ) =
% 0.60/0.77       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.60/0.77  thf('40', plain,
% 0.60/0.77      (![X11 : $i, X12 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X11 @ X12)
% 0.60/0.77           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.60/0.77              (k2_xboole_0 @ X11 @ X12)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.60/0.77  thf('41', plain,
% 0.60/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.60/0.77           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.60/0.77  thf('42', plain,
% 0.60/0.77      (![X11 : $i, X12 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X11 @ X12)
% 0.60/0.77           = (k5_xboole_0 @ X11 @ 
% 0.60/0.77              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.60/0.77      inference('demod', [status(thm)], ['40', '41'])).
% 0.60/0.77  thf('43', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.60/0.77           = (k5_xboole_0 @ X0 @ 
% 0.60/0.77              (k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.60/0.77               (k4_xboole_0 @ X0 @ k1_xboole_0))))),
% 0.60/0.77      inference('sup+', [status(thm)], ['39', '42'])).
% 0.60/0.77  thf('44', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['30', '33'])).
% 0.60/0.77  thf('45', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['4', '5'])).
% 0.60/0.77  thf('46', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['44', '45'])).
% 0.60/0.77  thf('47', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.60/0.77  thf('48', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['43', '46', '47'])).
% 0.60/0.77  thf('49', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.60/0.77  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['48', '49'])).
% 0.60/0.77  thf('51', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k2_xboole_0 @ X1 @ X0))),
% 0.60/0.77      inference('demod', [status(thm)], ['17', '50'])).
% 0.60/0.77  thf('52', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('sup+', [status(thm)], ['3', '51'])).
% 0.60/0.77  thf('53', plain,
% 0.60/0.77      (![X4 : $i, X5 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.60/0.77      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.60/0.77  thf('54', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.77           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.77  thf('55', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.60/0.77           = (k5_xboole_0 @ X0 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['53', '54'])).
% 0.60/0.77  thf('56', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.60/0.77  thf('57', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['55', '56'])).
% 0.60/0.77  thf('58', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X13 @ X14)
% 0.60/0.77           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.77  thf('59', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.60/0.77           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['57', '58'])).
% 0.60/0.77  thf('60', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.77  thf('61', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['14', '15'])).
% 0.60/0.77  thf('62', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.60/0.77  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['48', '49'])).
% 0.60/0.77  thf('64', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k2_xboole_0 @ X1 @ X0))),
% 0.60/0.77      inference('demod', [status(thm)], ['62', '63'])).
% 0.60/0.77  thf('65', plain,
% 0.60/0.77      (![X13 : $i, X14 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X13 @ X14)
% 0.60/0.77           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.77  thf('66', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.77  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['48', '49'])).
% 0.60/0.77  thf('68', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.60/0.77  thf('69', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['65', '68'])).
% 0.60/0.77  thf('70', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['64', '69'])).
% 0.60/0.77  thf('71', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0)
% 0.60/0.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['52', '70'])).
% 0.60/0.77  thf('72', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.77      inference('sup+', [status(thm)], ['3', '51'])).
% 0.60/0.77  thf('73', plain,
% 0.60/0.77      (![X11 : $i, X12 : $i]:
% 0.60/0.77         ((k3_xboole_0 @ X11 @ X12)
% 0.60/0.77           = (k5_xboole_0 @ X11 @ 
% 0.60/0.77              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.60/0.77      inference('demod', [status(thm)], ['40', '41'])).
% 0.60/0.77  thf('74', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.60/0.77  thf('75', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.77      inference('sup+', [status(thm)], ['73', '74'])).
% 0.60/0.77  thf('76', plain,
% 0.60/0.77      (![X2 : $i, X3 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ X2 @ X3)
% 0.60/0.77           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.60/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.60/0.77  thf('77', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.60/0.77           = (k4_xboole_0 @ X1 @ X0))),
% 0.60/0.77      inference('demod', [status(thm)], ['75', '76'])).
% 0.60/0.77  thf('78', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.60/0.77           = (k4_xboole_0 @ X1 @ X0))),
% 0.60/0.77      inference('demod', [status(thm)], ['71', '72', '77'])).
% 0.60/0.77  thf('79', plain,
% 0.60/0.77      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.60/0.77      inference('demod', [status(thm)], ['2', '78'])).
% 0.60/0.77  thf('80', plain,
% 0.60/0.77      ((((sk_C) != (sk_C))
% 0.60/0.77        | (r2_hidden @ sk_B @ sk_C)
% 0.60/0.77        | (r2_hidden @ sk_A @ sk_C))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '79'])).
% 0.60/0.77  thf('81', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.60/0.77      inference('simplify', [status(thm)], ['80'])).
% 0.60/0.77  thf('82', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('83', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.60/0.77      inference('clc', [status(thm)], ['81', '82'])).
% 0.60/0.77  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
