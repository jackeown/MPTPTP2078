%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FrkUM46ipt

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:30 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 164 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  615 (1158 expanded)
%              Number of equality atoms :   54 (  94 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['4','11'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference('sup+',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('67',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['17','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FrkUM46ipt
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:42:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 782 iterations in 0.292s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(t106_xboole_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.77       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.77        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.77          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t28_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf(t36_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf(t18_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.77         ((r1_tarski @ X9 @ X10)
% 0.59/0.77          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 0.59/0.77      inference('sup-', [status(thm)], ['5', '8'])).
% 0.59/0.77  thf(t49_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.59/0.77       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)) @ X0)),
% 0.59/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.77      inference('sup+', [status(thm)], ['4', '11'])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('14', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('16', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.59/0.77  thf('17', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.77      inference('sup+', [status(thm)], ['4', '11'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('21', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['24', '25'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.59/0.77           = (k4_xboole_0 @ sk_A @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['23', '26'])).
% 0.59/0.77  thf('28', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['18', '27'])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.59/0.77           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.77           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['31', '32'])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf(t100_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.77  thf('35', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X7 @ X8)
% 0.59/0.77           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['34', '35'])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.59/0.77           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['33', '36'])).
% 0.59/0.77  thf(t92_xboole_1, axiom,
% 0.59/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.59/0.77  thf('38', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.77           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['31', '32'])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.77         ((r1_tarski @ X9 @ X10)
% 0.59/0.77          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1)),
% 0.59/0.77      inference('sup-', [status(thm)], ['40', '43'])).
% 0.59/0.77  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.59/0.77      inference('sup+', [status(thm)], ['39', '44'])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('47', plain,
% 0.59/0.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.77  thf('48', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['34', '35'])).
% 0.59/0.77  thf('49', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['47', '48'])).
% 0.59/0.77  thf(t5_boole, axiom,
% 0.59/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.77  thf('50', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.59/0.77      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.77  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['49', '50'])).
% 0.59/0.77  thf('52', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('53', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('54', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.77         ((r1_tarski @ X9 @ X10)
% 0.59/0.77          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.59/0.77  thf('55', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X1)),
% 0.59/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.59/0.77  thf('56', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)) @ X1)),
% 0.59/0.77      inference('demod', [status(thm)], ['55', '56'])).
% 0.59/0.77  thf('58', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X0)),
% 0.59/0.77      inference('sup+', [status(thm)], ['52', '57'])).
% 0.59/0.77  thf('59', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)),
% 0.59/0.77      inference('sup+', [status(thm)], ['51', '58'])).
% 0.59/0.77  thf('60', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('61', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['59', '60'])).
% 0.59/0.77  thf('62', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('63', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['61', '62'])).
% 0.59/0.77  thf('64', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['34', '35'])).
% 0.59/0.77  thf('65', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.77           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['63', '64'])).
% 0.59/0.77  thf('66', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.59/0.77           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['24', '25'])).
% 0.59/0.77  thf('67', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.77  thf('68', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.59/0.77  thf('69', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['28', '68'])).
% 0.59/0.77  thf('70', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf(d7_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.77  thf('71', plain,
% 0.59/0.77      (![X4 : $i, X6 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.77  thf('72', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.77  thf('73', plain,
% 0.59/0.77      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['69', '72'])).
% 0.59/0.77  thf('74', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.59/0.77  thf('75', plain, ($false), inference('demod', [status(thm)], ['17', '74'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
