%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGCFDmZM8P

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:08 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 903 expanded)
%              Number of leaves         :   21 ( 319 expanded)
%              Depth                    :   21
%              Number of atoms          : 1035 (6730 expanded)
%              Number of equality atoms :  119 ( 888 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ X27 @ X26 )
      | ( X26
        = ( k4_xboole_0 @ X26 @ ( k2_tarski @ X25 @ X27 ) ) ) ) ),
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

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','25','26','29','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','25','26','29','32'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','64'])).

thf('66',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43','61','62'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('73',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('82',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(demod,[status(thm)],['77','80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','83'])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('87',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('98',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','100'])).

thf('102',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','103','104'])).

thf('106',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','105'])).

thf('107',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IGCFDmZM8P
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:17:12 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 856 iterations in 0.468s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(t145_zfmisc_1, conjecture,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.75/0.94          ( ( C ) !=
% 0.75/0.94            ( k4_xboole_0 @
% 0.75/0.94              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.75/0.94              ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.94        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.75/0.94             ( ( C ) !=
% 0.75/0.94               ( k4_xboole_0 @
% 0.75/0.94                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 0.75/0.94                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 0.75/0.94  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t144_zfmisc_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.75/0.94          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.94         ((r2_hidden @ X25 @ X26)
% 0.75/0.94          | (r2_hidden @ X27 @ X26)
% 0.75/0.94          | ((X26) = (k4_xboole_0 @ X26 @ (k2_tarski @ X25 @ X27))))),
% 0.75/0.94      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (((sk_C)
% 0.75/0.94         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.75/0.94             (k2_tarski @ sk_A @ sk_B)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.94  thf(t21_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      (![X5 : $i, X6 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.75/0.94      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.94  thf('5', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.94  thf(t100_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.94           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['5', '6'])).
% 0.75/0.94  thf(t1_boole, axiom,
% 0.75/0.94    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.94  thf('8', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X5 : $i, X6 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.75/0.94      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.94  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['8', '9'])).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.94           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['7', '12'])).
% 0.75/0.94  thf(t95_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k3_xboole_0 @ A @ B ) =
% 0.75/0.94       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.75/0.94              (k2_xboole_0 @ X11 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.75/0.94  thf(t91_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.94       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.75/0.94           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ X11 @ 
% 0.75/0.94              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.75/0.94      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.94  thf('17', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ X11 @ 
% 0.75/0.94              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.75/0.94      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.75/0.94           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['17', '18'])).
% 0.75/0.94  thf(t2_boole, axiom,
% 0.75/0.94    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_boole])).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['19', '20'])).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k1_xboole_0)
% 0.75/0.94           = (k5_xboole_0 @ 
% 0.75/0.94              (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.75/0.94              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['16', '21'])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.94  thf('24', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X5 : $i, X6 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.75/0.94      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['27', '28'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_boole])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.94           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['22', '25', '26', '29', '32'])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X5 : $i, X6 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.75/0.94      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.94           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.75/0.94           = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['34', '35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf(t99_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.94       ( k2_xboole_0 @
% 0.75/0.94         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.75/0.94         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.75/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)) @ 
% 0.75/0.94              (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X17))))),
% 0.75/0.94      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0)) @ 
% 0.75/0.94           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.75/0.94           = (k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['39', '40'])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.75/0.94           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 0.75/0.94           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['38', '41'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['22', '25', '26', '29', '32'])).
% 0.75/0.94  thf(t98_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X13 @ X14)
% 0.75/0.94           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 0.75/0.94           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['44', '45'])).
% 0.75/0.94  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X13 @ X14)
% 0.75/0.94           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X0 @ X0)
% 0.75/0.94           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['49', '50'])).
% 0.75/0.94  thf('52', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['7', '12'])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.94           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['52', '53'])).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.94           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['52', '53'])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['54', '55'])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X13 @ X14)
% 0.75/0.94           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.75/0.94           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['56', '57'])).
% 0.75/0.94  thf('59', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['51', '60'])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('63', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X0)
% 0.75/0.94           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.75/0.94      inference('demod', [status(thm)], ['42', '43', '61', '62'])).
% 0.75/0.94  thf('64', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['33', '63'])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['13', '64'])).
% 0.75/0.94  thf('66', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('67', plain,
% 0.75/0.94      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.75/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)) @ 
% 0.75/0.94              (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X17))))),
% 0.75/0.94      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.75/0.94  thf('68', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.75/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.75/0.94              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['66', '67'])).
% 0.75/0.94  thf('69', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.75/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['68', '69'])).
% 0.75/0.94  thf('71', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X0)
% 0.75/0.94           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.75/0.94      inference('demod', [status(thm)], ['42', '43', '61', '62'])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.75/0.94           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.94  thf('74', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.75/0.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['72', '73'])).
% 0.75/0.94  thf('75', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('76', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.75/0.94           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['74', '75'])).
% 0.75/0.94  thf('77', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) @ 
% 0.75/0.94           k1_xboole_0) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['71', '76'])).
% 0.75/0.94  thf('78', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.75/0.94  thf('79', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['58', '59'])).
% 0.75/0.94  thf('80', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('81', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['78', '79'])).
% 0.75/0.94  thf('82', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.75/0.94      inference('demod', [status(thm)], ['77', '80', '81'])).
% 0.75/0.94  thf('83', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ X1 @ X0)
% 0.75/0.94           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['70', '82'])).
% 0.75/0.94  thf('84', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.75/0.94              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['65', '83'])).
% 0.75/0.94  thf('85', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ X11 @ 
% 0.75/0.94              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.75/0.94      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.94  thf('86', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('87', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.75/0.94           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.94  thf('88', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.75/0.94           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['86', '87'])).
% 0.75/0.94  thf('89', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.75/0.94  thf('90', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.75/0.94  thf('91', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['89', '90'])).
% 0.75/0.94  thf('92', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.94  thf('93', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.75/0.94              (k2_xboole_0 @ X11 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.75/0.94  thf('94', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ X0)
% 0.75/0.94           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['92', '93'])).
% 0.75/0.94  thf('95', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['8', '9'])).
% 0.75/0.94  thf('96', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((X0)
% 0.75/0.94           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0)))),
% 0.75/0.94      inference('demod', [status(thm)], ['94', '95'])).
% 0.75/0.94  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['51', '60'])).
% 0.75/0.94  thf('98', plain,
% 0.75/0.94      (![X0 : $i]: ((X0) = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['96', '97'])).
% 0.75/0.94  thf('99', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X1) = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['91', '98'])).
% 0.75/0.94  thf('100', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['88', '99'])).
% 0.75/0.94  thf('101', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['85', '100'])).
% 0.75/0.94  thf('102', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X2 @ X3)
% 0.75/0.94           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('103', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['101', '102'])).
% 0.75/0.94  thf('104', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('105', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.94           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['84', '103', '104'])).
% 0.75/0.94  thf('106', plain,
% 0.75/0.94      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.75/0.94      inference('demod', [status(thm)], ['2', '105'])).
% 0.75/0.94  thf('107', plain,
% 0.75/0.94      ((((sk_C) != (sk_C))
% 0.75/0.94        | (r2_hidden @ sk_B @ sk_C)
% 0.75/0.94        | (r2_hidden @ sk_A @ sk_C))),
% 0.75/0.94      inference('sup-', [status(thm)], ['1', '106'])).
% 0.75/0.94  thf('108', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 0.75/0.94      inference('simplify', [status(thm)], ['107'])).
% 0.75/0.94  thf('109', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('110', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.75/0.94      inference('clc', [status(thm)], ['108', '109'])).
% 0.75/0.94  thf('111', plain, ($false), inference('demod', [status(thm)], ['0', '110'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
