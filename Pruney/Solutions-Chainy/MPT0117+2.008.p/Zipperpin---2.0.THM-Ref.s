%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d8BcQzRWfj

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:48 EST 2020

% Result     : Theorem 6.61s
% Output     : Refutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 351 expanded)
%              Number of leaves         :   22 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  727 (2384 expanded)
%              Number of equality atoms :   89 ( 292 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('20',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('45',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) ) @ ( k4_xboole_0 @ X27 @ ( k2_xboole_0 @ X26 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('59',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('61',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','54','65','70','71'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('74',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf('82',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d8BcQzRWfj
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.61/6.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.61/6.79  % Solved by: fo/fo7.sh
% 6.61/6.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.61/6.79  % done 3991 iterations in 6.337s
% 6.61/6.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.61/6.79  % SZS output start Refutation
% 6.61/6.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.61/6.79  thf(sk_C_type, type, sk_C: $i).
% 6.61/6.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.61/6.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.61/6.79  thf(sk_B_type, type, sk_B: $i).
% 6.61/6.79  thf(sk_A_type, type, sk_A: $i).
% 6.61/6.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.61/6.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.61/6.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.61/6.79  thf(t110_xboole_1, conjecture,
% 6.61/6.79    (![A:$i,B:$i,C:$i]:
% 6.61/6.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 6.61/6.79       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 6.61/6.79  thf(zf_stmt_0, negated_conjecture,
% 6.61/6.79    (~( ![A:$i,B:$i,C:$i]:
% 6.61/6.79        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 6.61/6.79          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 6.61/6.79    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 6.61/6.79  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 6.61/6.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.61/6.79  thf('1', plain, ((r1_tarski @ sk_C @ sk_B)),
% 6.61/6.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.61/6.79  thf(t28_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i]:
% 6.61/6.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.61/6.79  thf('2', plain,
% 6.61/6.79      (![X9 : $i, X10 : $i]:
% 6.61/6.79         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 6.61/6.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.61/6.79  thf('3', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 6.61/6.79      inference('sup-', [status(thm)], ['1', '2'])).
% 6.61/6.79  thf(t100_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i]:
% 6.61/6.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.61/6.79  thf('4', plain,
% 6.61/6.79      (![X2 : $i, X3 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X2 @ X3)
% 6.61/6.79           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.61/6.79  thf('5', plain,
% 6.61/6.79      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_C @ sk_C))),
% 6.61/6.79      inference('sup+', [status(thm)], ['3', '4'])).
% 6.61/6.79  thf(t92_xboole_1, axiom,
% 6.61/6.79    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 6.61/6.79  thf('6', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.61/6.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.61/6.79  thf('7', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 6.61/6.79      inference('demod', [status(thm)], ['5', '6'])).
% 6.61/6.79  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 6.61/6.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.61/6.79  thf('9', plain,
% 6.61/6.79      (![X9 : $i, X10 : $i]:
% 6.61/6.79         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 6.61/6.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.61/6.79  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 6.61/6.79      inference('sup-', [status(thm)], ['8', '9'])).
% 6.61/6.79  thf(commutativity_k3_xboole_0, axiom,
% 6.61/6.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.61/6.79  thf('11', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.61/6.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.61/6.79  thf('12', plain,
% 6.61/6.79      (![X2 : $i, X3 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X2 @ X3)
% 6.61/6.79           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.61/6.79  thf('13', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X0 @ X1)
% 6.61/6.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('sup+', [status(thm)], ['11', '12'])).
% 6.61/6.79  thf('14', plain,
% 6.61/6.79      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_A))),
% 6.61/6.79      inference('sup+', [status(thm)], ['10', '13'])).
% 6.61/6.79  thf(t91_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i,C:$i]:
% 6.61/6.79     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.61/6.79       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 6.61/6.79  thf('15', plain,
% 6.61/6.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 6.61/6.79           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.61/6.79  thf('16', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.61/6.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.61/6.79  thf('17', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 6.61/6.79           = (k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['15', '16'])).
% 6.61/6.79  thf('18', plain,
% 6.61/6.79      (((k5_xboole_0 @ sk_B @ 
% 6.61/6.79         (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))) = (k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['14', '17'])).
% 6.61/6.79  thf(t98_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i]:
% 6.61/6.79     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.61/6.79  thf('19', plain,
% 6.61/6.79      (![X24 : $i, X25 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ X24 @ X25)
% 6.61/6.79           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.61/6.79  thf('20', plain,
% 6.61/6.79      (((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 6.61/6.79      inference('demod', [status(thm)], ['18', '19'])).
% 6.61/6.79  thf('21', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.61/6.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.61/6.79  thf('22', plain,
% 6.61/6.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 6.61/6.79           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.61/6.79  thf('23', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 6.61/6.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('sup+', [status(thm)], ['21', '22'])).
% 6.61/6.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.61/6.79  thf('24', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 6.61/6.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.61/6.79  thf('25', plain,
% 6.61/6.79      (![X9 : $i, X10 : $i]:
% 6.61/6.79         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 6.61/6.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.61/6.79  thf('26', plain,
% 6.61/6.79      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.61/6.79      inference('sup-', [status(thm)], ['24', '25'])).
% 6.61/6.79  thf('27', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X0 @ X1)
% 6.61/6.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('sup+', [status(thm)], ['11', '12'])).
% 6.61/6.79  thf('28', plain,
% 6.61/6.79      (![X0 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['26', '27'])).
% 6.61/6.79  thf(t5_boole, axiom,
% 6.61/6.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.61/6.79  thf('29', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 6.61/6.79      inference('cnf', [status(esa)], [t5_boole])).
% 6.61/6.79  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['28', '29'])).
% 6.61/6.79  thf('31', plain,
% 6.61/6.79      (![X24 : $i, X25 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ X24 @ X25)
% 6.61/6.79           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.61/6.79  thf('32', plain,
% 6.61/6.79      (![X0 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['30', '31'])).
% 6.61/6.79  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['28', '29'])).
% 6.61/6.79  thf(t51_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i]:
% 6.61/6.79     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 6.61/6.79       ( A ) ))).
% 6.61/6.79  thf('34', plain,
% 6.61/6.79      (![X15 : $i, X16 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 6.61/6.79           = (X15))),
% 6.61/6.79      inference('cnf', [status(esa)], [t51_xboole_1])).
% 6.61/6.79  thf('35', plain,
% 6.61/6.79      (![X0 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['33', '34'])).
% 6.61/6.79  thf('36', plain,
% 6.61/6.79      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.61/6.79      inference('sup-', [status(thm)], ['24', '25'])).
% 6.61/6.79  thf('37', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.61/6.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.61/6.79  thf('38', plain,
% 6.61/6.79      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['36', '37'])).
% 6.61/6.79  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.61/6.79      inference('demod', [status(thm)], ['35', '38'])).
% 6.61/6.79  thf('40', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.61/6.79      inference('demod', [status(thm)], ['32', '39'])).
% 6.61/6.79  thf('41', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('demod', [status(thm)], ['23', '40'])).
% 6.61/6.79  thf('42', plain,
% 6.61/6.79      (((k2_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['20', '41'])).
% 6.61/6.79  thf('43', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 6.61/6.79      inference('cnf', [status(esa)], [t5_boole])).
% 6.61/6.79  thf('44', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 6.61/6.79      inference('demod', [status(thm)], ['42', '43'])).
% 6.61/6.79  thf(t99_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i,C:$i]:
% 6.61/6.79     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.61/6.79       ( k2_xboole_0 @
% 6.61/6.79         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 6.61/6.79         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 6.61/6.79  thf('45', plain,
% 6.61/6.79      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 6.61/6.79           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28)) @ 
% 6.61/6.79              (k4_xboole_0 @ X27 @ (k2_xboole_0 @ X26 @ X28))))),
% 6.61/6.79      inference('cnf', [status(esa)], [t99_xboole_1])).
% 6.61/6.79  thf('46', plain,
% 6.61/6.79      (![X0 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ sk_A) @ sk_B)
% 6.61/6.79           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 6.61/6.79              (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))))),
% 6.61/6.79      inference('sup+', [status(thm)], ['44', '45'])).
% 6.61/6.79  thf('47', plain,
% 6.61/6.79      (((k4_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 6.61/6.79         = (k2_xboole_0 @ k1_xboole_0 @ 
% 6.61/6.79            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))))),
% 6.61/6.79      inference('sup+', [status(thm)], ['7', '46'])).
% 6.61/6.79  thf('48', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 6.61/6.79           = (k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['15', '16'])).
% 6.61/6.79  thf('49', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('demod', [status(thm)], ['23', '40'])).
% 6.61/6.79  thf('50', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 6.61/6.79           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['48', '49'])).
% 6.61/6.79  thf('51', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 6.61/6.79      inference('cnf', [status(esa)], [t5_boole])).
% 6.61/6.79  thf('52', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 6.61/6.79      inference('demod', [status(thm)], ['50', '51'])).
% 6.61/6.79  thf('53', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('demod', [status(thm)], ['23', '40'])).
% 6.61/6.79  thf('54', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['52', '53'])).
% 6.61/6.79  thf('55', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 6.61/6.79      inference('sup-', [status(thm)], ['1', '2'])).
% 6.61/6.79  thf('56', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X0 @ X1)
% 6.61/6.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('sup+', [status(thm)], ['11', '12'])).
% 6.61/6.79  thf('57', plain,
% 6.61/6.79      (((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ sk_C))),
% 6.61/6.79      inference('sup+', [status(thm)], ['55', '56'])).
% 6.61/6.79  thf('58', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 6.61/6.79           = (k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['15', '16'])).
% 6.61/6.79  thf('59', plain,
% 6.61/6.79      (((k5_xboole_0 @ sk_B @ 
% 6.61/6.79         (k5_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['57', '58'])).
% 6.61/6.79  thf('60', plain,
% 6.61/6.79      (![X24 : $i, X25 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ X24 @ X25)
% 6.61/6.79           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.61/6.79  thf('61', plain,
% 6.61/6.79      (((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 6.61/6.79      inference('demod', [status(thm)], ['59', '60'])).
% 6.61/6.79  thf('62', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.61/6.79      inference('demod', [status(thm)], ['23', '40'])).
% 6.61/6.79  thf('63', plain,
% 6.61/6.79      (((k2_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['61', '62'])).
% 6.61/6.79  thf('64', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 6.61/6.79      inference('cnf', [status(esa)], [t5_boole])).
% 6.61/6.79  thf('65', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 6.61/6.79      inference('demod', [status(thm)], ['63', '64'])).
% 6.61/6.79  thf('66', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 6.61/6.79      inference('sup-', [status(thm)], ['8', '9'])).
% 6.61/6.79  thf('67', plain,
% 6.61/6.79      (![X2 : $i, X3 : $i]:
% 6.61/6.79         ((k4_xboole_0 @ X2 @ X3)
% 6.61/6.79           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.61/6.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.61/6.79  thf('68', plain,
% 6.61/6.79      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 6.61/6.79      inference('sup+', [status(thm)], ['66', '67'])).
% 6.61/6.79  thf('69', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.61/6.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.61/6.79  thf('70', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 6.61/6.79      inference('demod', [status(thm)], ['68', '69'])).
% 6.61/6.79  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.61/6.79      inference('demod', [status(thm)], ['35', '38'])).
% 6.61/6.79  thf('72', plain,
% 6.61/6.79      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 6.61/6.79      inference('demod', [status(thm)], ['47', '54', '65', '70', '71'])).
% 6.61/6.79  thf('73', plain,
% 6.61/6.79      (![X15 : $i, X16 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 6.61/6.79           = (X15))),
% 6.61/6.79      inference('cnf', [status(esa)], [t51_xboole_1])).
% 6.61/6.79  thf('74', plain,
% 6.61/6.79      (((k2_xboole_0 @ (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 6.61/6.79         k1_xboole_0) = (k5_xboole_0 @ sk_A @ sk_C))),
% 6.61/6.79      inference('sup+', [status(thm)], ['72', '73'])).
% 6.61/6.79  thf('75', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.61/6.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.61/6.79  thf('76', plain,
% 6.61/6.79      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.61/6.79      inference('sup-', [status(thm)], ['24', '25'])).
% 6.61/6.79  thf('77', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.61/6.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.61/6.79  thf(t22_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 6.61/6.79  thf('78', plain,
% 6.61/6.79      (![X7 : $i, X8 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 6.61/6.79      inference('cnf', [status(esa)], [t22_xboole_1])).
% 6.61/6.79  thf('79', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['77', '78'])).
% 6.61/6.79  thf('80', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.61/6.79      inference('sup+', [status(thm)], ['76', '79'])).
% 6.61/6.79  thf('81', plain,
% 6.61/6.79      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C))
% 6.61/6.79         = (k5_xboole_0 @ sk_A @ sk_C))),
% 6.61/6.79      inference('demod', [status(thm)], ['74', '75', '80'])).
% 6.61/6.79  thf('82', plain,
% 6.61/6.79      (![X15 : $i, X16 : $i]:
% 6.61/6.79         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 6.61/6.79           = (X15))),
% 6.61/6.79      inference('cnf', [status(esa)], [t51_xboole_1])).
% 6.61/6.79  thf(t7_xboole_1, axiom,
% 6.61/6.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.61/6.79  thf('83', plain,
% 6.61/6.79      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 6.61/6.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.61/6.79  thf('84', plain,
% 6.61/6.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 6.61/6.79      inference('sup+', [status(thm)], ['82', '83'])).
% 6.61/6.79  thf('85', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 6.61/6.79      inference('sup+', [status(thm)], ['81', '84'])).
% 6.61/6.79  thf('86', plain, ($false), inference('demod', [status(thm)], ['0', '85'])).
% 6.61/6.79  
% 6.61/6.79  % SZS output end Refutation
% 6.61/6.79  
% 6.61/6.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
