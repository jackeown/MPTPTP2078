%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.38G3tMDyAu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:47 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 483 expanded)
%              Number of leaves         :   21 ( 169 expanded)
%              Depth                    :   16
%              Number of atoms          :  848 (3240 expanded)
%              Number of equality atoms :  102 ( 404 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('34',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) @ ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_C ) @ sk_C )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_C ) @ sk_C ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ sk_C ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) @ ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_C @ X0 ) @ ( k5_xboole_0 @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_C @ sk_C ) ) ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_C ) @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_C @ X0 ) @ ( k5_xboole_0 @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_C ) @ sk_C ) ) @ ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_C @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('73',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) @ ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_C @ X0 )
      = ( k5_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','69','70','71','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_C ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('85',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('91',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','78','86','89','90'])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('95',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.38G3tMDyAu
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.70/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.92  % Solved by: fo/fo7.sh
% 0.70/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.92  % done 856 iterations in 0.468s
% 0.70/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.92  % SZS output start Refutation
% 0.70/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.92  thf(t110_xboole_1, conjecture,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.70/0.92       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.70/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.92        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.70/0.92          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.70/0.92    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.70/0.92  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('1', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf(t28_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.70/0.92  thf('2', plain,
% 0.70/0.92      (![X7 : $i, X8 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('3', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.70/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.92  thf(t100_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.92  thf('4', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.92  thf('5', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_C @ sk_C))),
% 0.70/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.70/0.92  thf(idempotence_k3_xboole_0, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.70/0.92  thf('6', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.70/0.92      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.70/0.92  thf('7', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.92  thf('8', plain,
% 0.70/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['6', '7'])).
% 0.70/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.92  thf('9', plain,
% 0.70/0.92      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.92  thf('10', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.92  thf('11', plain,
% 0.70/0.92      (![X7 : $i, X8 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('12', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.92  thf('13', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['9', '12'])).
% 0.70/0.92  thf('14', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.92  thf('15', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['13', '14'])).
% 0.70/0.92  thf(t5_boole, axiom,
% 0.70/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.92  thf('16', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.92  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.92  thf(t48_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.92  thf('18', plain,
% 0.70/0.92      (![X10 : $i, X11 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.70/0.92           = (k3_xboole_0 @ X10 @ X11))),
% 0.70/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.92  thf('19', plain,
% 0.70/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['17', '18'])).
% 0.70/0.92  thf('20', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['9', '12'])).
% 0.70/0.92  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['19', '20'])).
% 0.70/0.92  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('23', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['5', '22'])).
% 0.70/0.92  thf('24', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('25', plain,
% 0.70/0.92      (![X7 : $i, X8 : $i]:
% 0.70/0.92         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.70/0.92  thf('26', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.70/0.92      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.92  thf('27', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.92  thf('28', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.70/0.92      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.92  thf(t98_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.70/0.92  thf('29', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X15 @ X16)
% 0.70/0.92           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.92  thf('30', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.70/0.92         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['28', '29'])).
% 0.70/0.92  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.92  thf('31', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.92  thf('32', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.70/0.92         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 0.70/0.92      inference('demod', [status(thm)], ['30', '31'])).
% 0.70/0.92  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('34', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.92  thf('35', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.70/0.92      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.70/0.92  thf(t99_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i,C:$i]:
% 0.70/0.92     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.92       ( k2_xboole_0 @
% 0.70/0.92         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.70/0.92         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 0.70/0.92  thf('36', plain,
% 0.70/0.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.70/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)) @ 
% 0.70/0.92              (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X19))))),
% 0.70/0.92      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.70/0.92  thf('37', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ sk_A) @ sk_B)
% 0.70/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.70/0.92              (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['35', '36'])).
% 0.70/0.92  thf('38', plain,
% 0.70/0.92      (((k4_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 0.70/0.92         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.70/0.92            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['23', '37'])).
% 0.70/0.92  thf('39', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_C @ sk_C))),
% 0.70/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.70/0.92  thf('40', plain,
% 0.70/0.92      (![X10 : $i, X11 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.70/0.92           = (k3_xboole_0 @ X10 @ X11))),
% 0.70/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.92  thf('41', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_C @ sk_C))
% 0.70/0.92         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.70/0.92      inference('sup+', [status(thm)], ['39', '40'])).
% 0.70/0.92  thf('42', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.70/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.92  thf('43', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_C @ sk_C)) = (sk_C))),
% 0.70/0.92      inference('demod', [status(thm)], ['41', '42'])).
% 0.70/0.92  thf('44', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X15 @ X16)
% 0.70/0.92           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.92  thf('45', plain,
% 0.70/0.92      (((k2_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_C) @ sk_C)
% 0.70/0.92         = (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_C) @ sk_C))),
% 0.70/0.92      inference('sup+', [status(thm)], ['43', '44'])).
% 0.70/0.92  thf('46', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.92  thf('47', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_C @ sk_C))
% 0.70/0.92         = (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_C) @ sk_C))),
% 0.70/0.92      inference('demod', [status(thm)], ['45', '46'])).
% 0.70/0.92  thf('48', plain,
% 0.70/0.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.70/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)) @ 
% 0.70/0.92              (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X19))))),
% 0.70/0.92      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.70/0.92  thf('49', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ sk_C @ X0) @ 
% 0.70/0.92           (k5_xboole_0 @ sk_C @ sk_C))
% 0.70/0.92           = (k2_xboole_0 @ 
% 0.70/0.92              (k4_xboole_0 @ sk_C @ 
% 0.70/0.92               (k2_xboole_0 @ X0 @ (k5_xboole_0 @ sk_C @ sk_C))) @ 
% 0.70/0.92              (k4_xboole_0 @ X0 @ 
% 0.70/0.92               (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_C) @ sk_C))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['47', '48'])).
% 0.70/0.92  thf('50', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.92  thf('51', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ sk_C @ X0) @ 
% 0.70/0.92           (k5_xboole_0 @ sk_C @ sk_C))
% 0.70/0.92           = (k2_xboole_0 @ 
% 0.70/0.92              (k4_xboole_0 @ X0 @ 
% 0.70/0.92               (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_C) @ sk_C)) @ 
% 0.70/0.92              (k4_xboole_0 @ sk_C @ 
% 0.70/0.92               (k2_xboole_0 @ X0 @ (k5_xboole_0 @ sk_C @ sk_C)))))),
% 0.70/0.92      inference('demod', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('52', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.92  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.92  thf('56', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X15 @ X16)
% 0.70/0.92           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.92  thf('57', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['55', '56'])).
% 0.70/0.92  thf('58', plain,
% 0.70/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.92  thf('59', plain,
% 0.70/0.92      (![X5 : $i, X6 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ X5 @ X6)
% 0.70/0.92           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.92  thf('60', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.70/0.92           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['58', '59'])).
% 0.70/0.92  thf('61', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.92  thf('62', plain,
% 0.70/0.92      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['60', '61'])).
% 0.70/0.92  thf('63', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X15 @ X16)
% 0.70/0.92           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.92  thf('64', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['62', '63'])).
% 0.70/0.92  thf('65', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.92  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.92  thf('67', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.92  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['66', '67'])).
% 0.70/0.92  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['57', '68'])).
% 0.70/0.92  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.92  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.92  thf('73', plain,
% 0.70/0.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.70/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)) @ 
% 0.70/0.92              (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X19))))),
% 0.70/0.92      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.70/0.92  thf('74', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.70/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.70/0.92              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0))))),
% 0.70/0.92      inference('sup+', [status(thm)], ['72', '73'])).
% 0.70/0.92  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.92  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.92  thf('77', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((k5_xboole_0 @ X1 @ X0)
% 0.70/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.70/0.92      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.70/0.92  thf('78', plain,
% 0.70/0.92      (![X0 : $i]: ((k5_xboole_0 @ sk_C @ X0) = (k5_xboole_0 @ X0 @ sk_C))),
% 0.70/0.92      inference('demod', [status(thm)],
% 0.70/0.92                ['51', '52', '53', '54', '69', '70', '71', '77'])).
% 0.70/0.92  thf('79', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_C @ sk_C))),
% 0.70/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.70/0.92  thf('80', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X15 @ X16)
% 0.70/0.92           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.92  thf('81', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_B @ sk_C)
% 0.70/0.92         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_C)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['79', '80'])).
% 0.70/0.92  thf('82', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.92  thf('83', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_C @ sk_B)
% 0.70/0.92         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_C)))),
% 0.70/0.92      inference('demod', [status(thm)], ['81', '82'])).
% 0.70/0.92  thf('84', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('85', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.92  thf('86', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.70/0.92      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.70/0.92  thf('87', plain,
% 0.70/0.92      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.70/0.92      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.92  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['8', '21'])).
% 0.70/0.92  thf('89', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['87', '88'])).
% 0.70/0.92  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['66', '67'])).
% 0.70/0.92  thf('91', plain,
% 0.70/0.92      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['38', '78', '86', '89', '90'])).
% 0.70/0.92  thf('92', plain,
% 0.70/0.92      (![X15 : $i, X16 : $i]:
% 0.70/0.92         ((k2_xboole_0 @ X15 @ X16)
% 0.70/0.92           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.70/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.70/0.92  thf('93', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.70/0.92         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['91', '92'])).
% 0.70/0.92  thf('94', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.92  thf('95', plain,
% 0.70/0.92      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.70/0.92      inference('demod', [status(thm)], ['93', '94'])).
% 0.70/0.92  thf('96', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.92  thf(t7_xboole_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.92  thf('97', plain,
% 0.70/0.92      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.70/0.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.70/0.92  thf('98', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['96', '97'])).
% 0.70/0.92  thf('99', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.70/0.92      inference('sup+', [status(thm)], ['95', '98'])).
% 0.70/0.92  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.70/0.92  
% 0.70/0.92  % SZS output end Refutation
% 0.70/0.92  
% 0.76/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
