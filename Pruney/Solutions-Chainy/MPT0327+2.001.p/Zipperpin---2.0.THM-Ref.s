%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SbuZSNhbAh

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:50 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 212 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  754 (1651 expanded)
%              Number of equality atoms :   77 ( 158 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('4',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X40: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X40 @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r2_hidden @ X40 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['8','9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('29',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','26','27','28'])).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['2','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','41','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('56',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('63',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','48','61','62'])).

thf('64',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X38 @ X39 ) )
      = ( k2_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SbuZSNhbAh
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 480 iterations in 0.179s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(t94_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ A @ B ) =
% 0.45/0.64       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.64           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.45/0.64              (k3_xboole_0 @ X24 @ X25)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.45/0.64  thf(t91_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.64       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.45/0.64           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.64           = (k5_xboole_0 @ X24 @ 
% 0.45/0.64              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.64  thf(t48_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.64           = (k3_xboole_0 @ X15 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf(t140_zfmisc_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r2_hidden @ A @ B ) =>
% 0.45/0.64       ( ( k2_xboole_0 @
% 0.45/0.64           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.45/0.64         ( B ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i]:
% 0.45/0.64        ( ( r2_hidden @ A @ B ) =>
% 0.45/0.64          ( ( k2_xboole_0 @
% 0.45/0.64              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.45/0.64            ( B ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.45/0.64  thf('4', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('5', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t38_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.45/0.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X40 : $i, X42 : $i, X43 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_tarski @ X40 @ X42) @ X43)
% 0.45/0.64          | ~ (r2_hidden @ X42 @ X43)
% 0.45/0.64          | ~ (r2_hidden @ X40 @ X43))),
% 0.45/0.64      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.64          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('8', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.64  thf(t69_enumset1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.64  thf('9', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.64  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf(t28_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf(t49_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.64       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.45/0.64           = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf(t100_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X5 @ X6)
% 0.45/0.64           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.45/0.64           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_B @ 
% 0.45/0.64           (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64            (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))
% 0.45/0.64           = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['3', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.64           = (k3_xboole_0 @ X15 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.45/0.64           = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.64           = (k5_xboole_0 @ X24 @ 
% 0.45/0.64              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.45/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.64  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf(t12_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i]:
% 0.45/0.64         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.45/0.64  thf('26', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (((sk_B)
% 0.45/0.64         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['23', '26', '27', '28'])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.45/0.64           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k5_xboole_0 @ sk_B @ X0)
% 0.45/0.64           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64              (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (((k5_xboole_0 @ sk_B @ 
% 0.45/0.64         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.45/0.64         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('sup+', [status(thm)], ['2', '31'])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.64           = (k3_xboole_0 @ X15 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.45/0.64           = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.45/0.64           = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64              (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['34', '35'])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.64           = (k3_xboole_0 @ X15 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.45/0.64           = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.45/0.64           = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['33', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X5 @ X6)
% 0.45/0.64           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.45/0.64           = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (((k4_xboole_0 @ sk_B @ 
% 0.45/0.64         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.45/0.64         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['32', '41', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.45/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.45/0.64      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 0.45/0.64           = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['44', '47'])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('49', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.45/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['51', '52'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X5 @ X6)
% 0.45/0.64           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf(t5_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.64  thf('56', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.45/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.64  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.64           = (k3_xboole_0 @ X15 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['51', '52'])).
% 0.45/0.64  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.64  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      (((sk_B)
% 0.45/0.64         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '48', '61', '62'])).
% 0.45/0.64  thf('64', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.64         (k1_tarski @ sk_A)) != (sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(commutativity_k2_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i]:
% 0.45/0.64         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.64  thf(l51_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X38 : $i, X39 : $i]:
% 0.45/0.64         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.45/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.64  thf('68', plain,
% 0.45/0.64      (![X38 : $i, X39 : $i]:
% 0.45/0.64         ((k3_tarski @ (k2_tarski @ X38 @ X39)) = (k2_xboole_0 @ X38 @ X39))),
% 0.45/0.64      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.45/0.64         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['64', '69'])).
% 0.45/0.64  thf('71', plain, ($false),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['63', '70'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
