%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.68AEkLnxc0

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:36 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 557 expanded)
%              Number of leaves         :   22 ( 192 expanded)
%              Depth                    :   21
%              Number of atoms          : 1003 (3998 expanded)
%              Number of equality atoms :  111 ( 420 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','7'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('66',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','71'])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('78',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['35','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('81',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['79','88'])).

thf('90',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('92',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('99',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['96','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['13','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.68AEkLnxc0
% 0.15/0.38  % Computer   : n012.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:16:37 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 1.29/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.50  % Solved by: fo/fo7.sh
% 1.29/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.50  % done 2129 iterations in 1.006s
% 1.29/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.50  % SZS output start Refutation
% 1.29/1.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.29/1.50  thf(sk_C_type, type, sk_C: $i).
% 1.29/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.29/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.29/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.29/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.29/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.50  thf(t106_xboole_1, conjecture,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.29/1.50       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.29/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.50    (~( ![A:$i,B:$i,C:$i]:
% 1.29/1.50        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.29/1.50          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 1.29/1.50    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 1.29/1.50  thf('0', plain,
% 1.29/1.50      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf('1', plain,
% 1.29/1.50      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 1.29/1.50      inference('split', [status(esa)], ['0'])).
% 1.29/1.50  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.29/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.50  thf(t28_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i]:
% 1.29/1.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.29/1.50  thf('3', plain,
% 1.29/1.50      (![X13 : $i, X14 : $i]:
% 1.29/1.50         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.29/1.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.29/1.50  thf('4', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.29/1.50      inference('sup-', [status(thm)], ['2', '3'])).
% 1.29/1.50  thf(t49_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.29/1.50       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.29/1.50  thf('5', plain,
% 1.29/1.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.29/1.50           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.29/1.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.29/1.50  thf(t79_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.29/1.50  thf('6', plain,
% 1.29/1.50      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 1.29/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.29/1.50  thf('7', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 1.29/1.50      inference('sup+', [status(thm)], ['5', '6'])).
% 1.29/1.50  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.29/1.50      inference('sup+', [status(thm)], ['4', '7'])).
% 1.29/1.50  thf('9', plain,
% 1.29/1.50      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.29/1.50      inference('split', [status(esa)], ['0'])).
% 1.29/1.50  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.29/1.50      inference('sup-', [status(thm)], ['8', '9'])).
% 1.29/1.50  thf('11', plain,
% 1.29/1.50      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 1.29/1.50      inference('split', [status(esa)], ['0'])).
% 1.29/1.50  thf('12', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 1.29/1.50      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 1.29/1.50  thf('13', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.29/1.50      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 1.29/1.50  thf('14', plain,
% 1.29/1.50      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 1.29/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.29/1.50  thf(d7_xboole_0, axiom,
% 1.29/1.50    (![A:$i,B:$i]:
% 1.29/1.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.29/1.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.29/1.50  thf('15', plain,
% 1.29/1.50      (![X2 : $i, X3 : $i]:
% 1.29/1.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.29/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.29/1.50  thf('16', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.50  thf(t100_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i]:
% 1.29/1.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.29/1.50  thf('17', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X8 @ X9)
% 1.29/1.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.29/1.50  thf('18', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.29/1.50           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['16', '17'])).
% 1.29/1.50  thf(commutativity_k5_xboole_0, axiom,
% 1.29/1.50    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.29/1.50  thf('19', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.29/1.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.29/1.50  thf('20', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.29/1.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.29/1.50  thf(t5_boole, axiom,
% 1.29/1.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.29/1.50  thf('21', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.29/1.50      inference('cnf', [status(esa)], [t5_boole])).
% 1.29/1.50  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['20', '21'])).
% 1.29/1.50  thf('23', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.29/1.50           = (k4_xboole_0 @ X1 @ X0))),
% 1.29/1.50      inference('demod', [status(thm)], ['18', '19', '22'])).
% 1.29/1.50  thf(t98_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i]:
% 1.29/1.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.29/1.50  thf('24', plain,
% 1.29/1.50      (![X25 : $i, X26 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X25 @ X26)
% 1.29/1.50           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.29/1.50  thf('25', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.29/1.50           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['23', '24'])).
% 1.29/1.50  thf('26', plain,
% 1.29/1.50      (![X25 : $i, X26 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X25 @ X26)
% 1.29/1.50           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.29/1.50  thf('27', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ X1)
% 1.29/1.50           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['25', '26'])).
% 1.29/1.50  thf('28', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.29/1.50      inference('sup-', [status(thm)], ['2', '3'])).
% 1.29/1.50  thf(t23_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i,C:$i]:
% 1.29/1.50     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.29/1.50       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.29/1.50  thf('29', plain,
% 1.29/1.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 1.29/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 1.29/1.50              (k3_xboole_0 @ X10 @ X12)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.29/1.50  thf('30', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ 
% 1.29/1.50           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 1.29/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['28', '29'])).
% 1.29/1.50  thf('31', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 1.29/1.50         = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['27', '30'])).
% 1.29/1.50  thf('32', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.29/1.50      inference('sup+', [status(thm)], ['4', '7'])).
% 1.29/1.50  thf('33', plain,
% 1.29/1.50      (![X2 : $i, X3 : $i]:
% 1.29/1.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.29/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.29/1.50  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['32', '33'])).
% 1.29/1.50  thf('35', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 1.29/1.50         = (k2_xboole_0 @ k1_xboole_0 @ sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['31', '34'])).
% 1.29/1.50  thf('36', plain,
% 1.29/1.50      (![X25 : $i, X26 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X25 @ X26)
% 1.29/1.50           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.29/1.50  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['20', '21'])).
% 1.29/1.50  thf('38', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['36', '37'])).
% 1.29/1.50  thf('39', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['32', '33'])).
% 1.29/1.50  thf('40', plain,
% 1.29/1.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.29/1.50           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.29/1.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.29/1.50  thf('41', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))
% 1.29/1.50           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['39', '40'])).
% 1.29/1.50  thf('42', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.50  thf('43', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 1.29/1.50      inference('sup+', [status(thm)], ['5', '6'])).
% 1.29/1.50  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.29/1.50      inference('sup+', [status(thm)], ['42', '43'])).
% 1.29/1.50  thf('45', plain,
% 1.29/1.50      (![X2 : $i, X3 : $i]:
% 1.29/1.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.29/1.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.29/1.50  thf('46', plain,
% 1.29/1.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['44', '45'])).
% 1.29/1.50  thf('47', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X8 @ X9)
% 1.29/1.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.29/1.50  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['20', '21'])).
% 1.29/1.50  thf('49', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['47', '48'])).
% 1.29/1.50  thf('50', plain,
% 1.29/1.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['46', '49'])).
% 1.29/1.50  thf('51', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)) = (k1_xboole_0))),
% 1.29/1.50      inference('demod', [status(thm)], ['41', '50'])).
% 1.29/1.50  thf('52', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.29/1.50         = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['38', '51'])).
% 1.29/1.50  thf('53', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['32', '33'])).
% 1.29/1.50  thf('54', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X8 @ X9)
% 1.29/1.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.29/1.50  thf('55', plain,
% 1.29/1.50      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['53', '54'])).
% 1.29/1.50  thf('56', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.29/1.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.29/1.50  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['20', '21'])).
% 1.29/1.50  thf('58', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.29/1.50  thf('59', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.50  thf('60', plain,
% 1.29/1.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 1.29/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 1.29/1.50              (k3_xboole_0 @ X10 @ X12)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.29/1.50  thf('61', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0))
% 1.29/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 1.29/1.50              k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['59', '60'])).
% 1.29/1.50  thf('62', plain,
% 1.29/1.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['46', '49'])).
% 1.29/1.50  thf('63', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.29/1.50           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['23', '24'])).
% 1.29/1.50  thf('64', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 1.29/1.50           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['62', '63'])).
% 1.29/1.50  thf('65', plain,
% 1.29/1.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['46', '49'])).
% 1.29/1.50  thf('66', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.29/1.50      inference('cnf', [status(esa)], [t5_boole])).
% 1.29/1.50  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.29/1.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.29/1.50  thf('68', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0))
% 1.29/1.50           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 1.29/1.50      inference('demod', [status(thm)], ['61', '67'])).
% 1.29/1.50  thf('69', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 1.29/1.50           = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['58', '68'])).
% 1.29/1.50  thf('70', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.29/1.50  thf('71', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 1.29/1.50           = (k3_xboole_0 @ sk_A @ X0))),
% 1.29/1.50      inference('demod', [status(thm)], ['69', '70'])).
% 1.29/1.50  thf('72', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 1.29/1.50      inference('demod', [status(thm)], ['52', '71'])).
% 1.29/1.50  thf('73', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X8 @ X9)
% 1.29/1.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.29/1.50  thf('74', plain,
% 1.29/1.50      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['72', '73'])).
% 1.29/1.50  thf('75', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['36', '37'])).
% 1.29/1.50  thf('76', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.29/1.50      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.29/1.50  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['20', '21'])).
% 1.29/1.50  thf('78', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 1.29/1.50  thf('79', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) = (sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['35', '78'])).
% 1.29/1.50  thf('80', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.29/1.50      inference('sup-', [status(thm)], ['32', '33'])).
% 1.29/1.50  thf('81', plain,
% 1.29/1.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 1.29/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 1.29/1.50              (k3_xboole_0 @ X10 @ X12)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.29/1.50  thf('82', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 1.29/1.50           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['80', '81'])).
% 1.29/1.50  thf('83', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['36', '37'])).
% 1.29/1.50  thf('84', plain,
% 1.29/1.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.29/1.50           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.29/1.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.29/1.50  thf('85', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 1.29/1.50           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['83', '84'])).
% 1.29/1.50  thf('86', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['36', '37'])).
% 1.29/1.50  thf('87', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 1.29/1.50           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.50      inference('demod', [status(thm)], ['85', '86'])).
% 1.29/1.50  thf('88', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 1.29/1.50           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.29/1.50      inference('demod', [status(thm)], ['82', '87'])).
% 1.29/1.50  thf('89', plain,
% 1.29/1.50      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B)) = (sk_A))),
% 1.29/1.50      inference('demod', [status(thm)], ['79', '88'])).
% 1.29/1.50  thf('90', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X8 @ X9)
% 1.29/1.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.29/1.50  thf('91', plain,
% 1.29/1.50      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))
% 1.29/1.50         = (k5_xboole_0 @ sk_A @ sk_A))),
% 1.29/1.50      inference('sup+', [status(thm)], ['89', '90'])).
% 1.29/1.50  thf(t92_xboole_1, axiom,
% 1.29/1.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.29/1.50  thf('92', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 1.29/1.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.29/1.50  thf('93', plain,
% 1.29/1.50      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))
% 1.29/1.50         = (k1_xboole_0))),
% 1.29/1.50      inference('demod', [status(thm)], ['91', '92'])).
% 1.29/1.50  thf(l32_xboole_1, axiom,
% 1.29/1.50    (![A:$i,B:$i]:
% 1.29/1.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.29/1.50  thf('94', plain,
% 1.29/1.50      (![X5 : $i, X6 : $i]:
% 1.29/1.50         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.29/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.29/1.50  thf('95', plain,
% 1.29/1.50      ((((k1_xboole_0) != (k1_xboole_0))
% 1.29/1.50        | (r1_tarski @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 1.29/1.50      inference('sup-', [status(thm)], ['93', '94'])).
% 1.29/1.50  thf('96', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 1.29/1.50      inference('simplify', [status(thm)], ['95'])).
% 1.29/1.50  thf('97', plain,
% 1.29/1.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['46', '49'])).
% 1.29/1.50  thf('98', plain,
% 1.29/1.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.29/1.50           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.29/1.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.29/1.50  thf('99', plain,
% 1.29/1.50      (![X25 : $i, X26 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X25 @ X26)
% 1.29/1.50           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.29/1.50  thf('100', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.29/1.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.29/1.50      inference('sup+', [status(thm)], ['98', '99'])).
% 1.29/1.50  thf('101', plain,
% 1.29/1.50      (![X8 : $i, X9 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X8 @ X9)
% 1.29/1.50           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.29/1.50  thf('102', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 1.29/1.50           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['100', '101'])).
% 1.29/1.50  thf('103', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.29/1.50           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['97', '102'])).
% 1.29/1.50  thf('104', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['36', '37'])).
% 1.29/1.50  thf('105', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.29/1.50           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.29/1.50      inference('demod', [status(thm)], ['103', '104'])).
% 1.29/1.50  thf('106', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 1.29/1.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.29/1.50  thf('107', plain,
% 1.29/1.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['46', '49'])).
% 1.29/1.50  thf('108', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.29/1.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.29/1.50      inference('sup+', [status(thm)], ['98', '99'])).
% 1.29/1.50  thf('109', plain,
% 1.29/1.50      (![X0 : $i, X1 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 1.29/1.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 1.29/1.50      inference('sup+', [status(thm)], ['107', '108'])).
% 1.29/1.50  thf('110', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.29/1.50           (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.29/1.50      inference('sup+', [status(thm)], ['106', '109'])).
% 1.29/1.50  thf('111', plain,
% 1.29/1.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.29/1.50         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 1.29/1.50           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 1.29/1.50              (k3_xboole_0 @ X10 @ X12)))),
% 1.29/1.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.29/1.50  thf('112', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.29/1.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.29/1.50  thf('113', plain,
% 1.29/1.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.29/1.50      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.29/1.50  thf('114', plain,
% 1.29/1.50      (![X0 : $i]:
% 1.29/1.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.29/1.50      inference('demod', [status(thm)], ['105', '113'])).
% 1.29/1.50  thf('115', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.29/1.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.29/1.50  thf('116', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.29/1.50      inference('demod', [status(thm)], ['114', '115'])).
% 1.29/1.50  thf('117', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.29/1.50      inference('demod', [status(thm)], ['96', '116'])).
% 1.29/1.50  thf('118', plain, ($false), inference('demod', [status(thm)], ['13', '117'])).
% 1.29/1.50  
% 1.29/1.50  % SZS output end Refutation
% 1.29/1.50  
% 1.29/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
