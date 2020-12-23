%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FPcEuPtHDK

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:56 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 756 expanded)
%              Number of leaves         :   21 ( 256 expanded)
%              Depth                    :   16
%              Number of atoms          :  787 (5647 expanded)
%              Number of equality atoms :   96 ( 671 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_D ) @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['14','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','38'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('67',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','38'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['62','73','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('78',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('80',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('82',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['40','43'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['75','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['49','87'])).

thf('89',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('91',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['75','86'])).

thf('93',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('94',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['75','86'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['67','68'])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['88','96'])).

thf('98',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FPcEuPtHDK
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 743 iterations in 0.288s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(t72_xboole_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.52/0.73         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.52/0.73       ( ( C ) = ( B ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.52/0.73            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.52/0.73          ( ( C ) = ( B ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.52/0.73  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(d7_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.52/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.52/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.73  thf('2', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.52/0.73  thf(t51_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.52/0.73       ( A ) ))).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X20 : $i, X21 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.52/0.73           = (X20))),
% 0.52/0.73      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.73  thf(t3_boole, axiom,
% 0.52/0.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.73  thf('7', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf(t40_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf('10', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['6', '13'])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf(t48_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.52/0.73           = (k3_xboole_0 @ X18 @ X19))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf(t7_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.52/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.73  thf(t12_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.52/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.73  thf(t43_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.52/0.73       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.52/0.73          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.52/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.73  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['25', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.52/0.73           = (k3_xboole_0 @ X18 @ X19))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.52/0.73           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['20', '37'])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['19', '38'])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_D) @ sk_B) = (sk_D))),
% 0.52/0.73      inference('sup+', [status(thm)], ['14', '39'])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.73           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('sup+', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('44', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['40', '43'])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['19', '38'])).
% 0.52/0.73  thf('46', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_D) = (sk_B))),
% 0.52/0.73      inference('sup+', [status(thm)], ['44', '45'])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('49', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.52/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['50', '51'])).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('54', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.52/0.73          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.52/0.73  thf('57', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.52/0.73          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 0.52/0.73      inference('sup-', [status(thm)], ['55', '56'])).
% 0.52/0.73  thf('58', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D)),
% 0.52/0.73      inference('sup-', [status(thm)], ['52', '57'])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.73  thf('60', plain,
% 0.52/0.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_D) = (sk_D))),
% 0.52/0.73      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.73  thf('61', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('62', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['60', '61'])).
% 0.52/0.73  thf('63', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('64', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.52/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.73  thf('65', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.73  thf('66', plain,
% 0.52/0.73      (![X20 : $i, X21 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.52/0.73           = (X20))),
% 0.52/0.73      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.52/0.73  thf('67', plain,
% 0.52/0.73      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['65', '66'])).
% 0.52/0.73  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('69', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.73  thf('70', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.73           = (X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['19', '38'])).
% 0.52/0.73  thf('71', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_C) = (sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['69', '70'])).
% 0.52/0.73  thf('72', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.73           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('sup+', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('73', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['71', '72'])).
% 0.52/0.73  thf('74', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('75', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['62', '73', '74'])).
% 0.52/0.73  thf('76', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.52/0.73  thf('77', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['50', '51'])).
% 0.52/0.73  thf('78', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['76', '77'])).
% 0.52/0.73  thf('79', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.52/0.73          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.52/0.73  thf('80', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A)),
% 0.52/0.73      inference('sup-', [status(thm)], ['78', '79'])).
% 0.52/0.73  thf('81', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.73  thf('82', plain,
% 0.52/0.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['80', '81'])).
% 0.52/0.73  thf('83', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('84', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['82', '83'])).
% 0.52/0.73  thf('85', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['40', '43'])).
% 0.52/0.73  thf('86', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['84', '85'])).
% 0.52/0.73  thf('87', plain, (((sk_D) = (sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['75', '86'])).
% 0.52/0.73  thf('88', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['49', '87'])).
% 0.52/0.73  thf('89', plain,
% 0.52/0.73      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.52/0.73  thf('90', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('91', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 0.52/0.73         = (k4_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.73      inference('sup+', [status(thm)], ['89', '90'])).
% 0.52/0.73  thf('92', plain, (((sk_D) = (sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['75', '86'])).
% 0.52/0.73  thf('93', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 0.52/0.73           = (k4_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.52/0.73  thf('94', plain, (((sk_D) = (sk_A))),
% 0.52/0.73      inference('sup+', [status(thm)], ['75', '86'])).
% 0.52/0.73  thf('95', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.73  thf('96', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.52/0.73  thf('97', plain, (((sk_B) = (sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['88', '96'])).
% 0.52/0.73  thf('98', plain, (((sk_C) != (sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('99', plain, ($false),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
