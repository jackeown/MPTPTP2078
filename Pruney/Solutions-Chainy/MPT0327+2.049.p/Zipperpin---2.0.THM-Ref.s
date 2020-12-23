%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KZ5CV6IW7I

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:56 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  156 (1312 expanded)
%              Number of leaves         :   24 ( 439 expanded)
%              Depth                    :   22
%              Number of atoms          : 1259 (9443 expanded)
%              Number of equality atoms :  133 (1053 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('49',plain,(
    ! [X33: $i] :
      ( r1_tarski @ X33 @ ( k1_zfmisc_1 @ ( k3_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X33: $i] :
      ( r1_tarski @ X33 @ ( k1_zfmisc_1 @ ( k3_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('55',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('93',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('106',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','106'])).

thf('108',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('113',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('116',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('118',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','118'])).

thf('120',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['110','119'])).

thf('121',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('126',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('128',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['37','126','127'])).

thf('129',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KZ5CV6IW7I
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:16:22 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 304 iterations in 0.164s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(t140_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.66       ( ( k2_xboole_0 @
% 0.46/0.66           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.46/0.66         ( B ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( r2_hidden @ A @ B ) =>
% 0.46/0.66          ( ( k2_xboole_0 @
% 0.46/0.66              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.46/0.66            ( B ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.46/0.66  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(l1_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X28 : $i, X30 : $i]:
% 0.46/0.66         ((r1_tarski @ (k1_tarski @ X28) @ X30) | ~ (r2_hidden @ X28 @ X30))),
% 0.46/0.66      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.46/0.66  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf(t28_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf(t100_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t94_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.66       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.46/0.66              (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66            (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.66  thf(l32_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X2 : $i, X4 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf(t39_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.46/0.66           = (k2_xboole_0 @ X10 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.46/0.66         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.46/0.66         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66            (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.46/0.66              (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66         (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 0.46/0.66            (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66             (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66         (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 0.46/0.66            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.66  thf('22', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.46/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf(t3_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.66  thf('29', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.66  thf('30', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.46/0.66              (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('35', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('36', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66         (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ 
% 0.46/0.66            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t91_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.66       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.46/0.66           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66           (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.46/0.66           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['38', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.46/0.66              (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ X16 @ 
% 0.46/0.66              (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X16 @ X17))))),
% 0.46/0.66      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66            (k5_xboole_0 @ sk_B @ 
% 0.46/0.66             (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.46/0.66           = (k2_xboole_0 @ X10 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66            (k5_xboole_0 @ sk_B @ 
% 0.46/0.66             (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.46/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf(t100_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X33 : $i]: (r1_tarski @ X33 @ (k1_zfmisc_1 @ (k3_tarski @ X33)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))) = (X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.46/0.66           = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X33 : $i]: (r1_tarski @ X33 @ (k1_zfmisc_1 @ (k3_tarski @ X33)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X2 : $i, X4 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.66  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['53', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.46/0.66              (k3_xboole_0 @ X16 @ X17)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.66  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['53', '56'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('69', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('70', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['65', '70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (((k5_xboole_0 @ sk_B @ 
% 0.46/0.66         (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.46/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66            (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['48', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X16 @ X17)
% 0.46/0.66           = (k5_xboole_0 @ X16 @ 
% 0.46/0.66              (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X16 @ X17))))),
% 0.46/0.66      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['79', '80'])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['78', '81'])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      (((k1_xboole_0) = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['89', '90'])).
% 0.46/0.66  thf('92', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['92', '93'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.46/0.66      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['91', '96'])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['88', '97'])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.46/0.66      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['99', '100'])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['98', '103'])).
% 0.46/0.66  thf('105', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['104', '105'])).
% 0.46/0.66  thf('107', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['77', '106'])).
% 0.46/0.66  thf('108', plain,
% 0.46/0.66      (((k5_xboole_0 @ sk_B @ 
% 0.46/0.66         (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.46/0.66         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['72', '107'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['65', '70'])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('112', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['59', '64'])).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['111', '112'])).
% 0.46/0.66  thf('114', plain,
% 0.46/0.66      (((k1_xboole_0) = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.46/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['114', '115'])).
% 0.46/0.66  thf('117', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['116', '117'])).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      (((k1_tarski @ sk_A)
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['113', '118'])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['110', '119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('122', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['104', '105'])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66              (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['121', '122'])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['120', '123'])).
% 0.46/0.66  thf('125', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['53', '56'])).
% 0.46/0.66  thf('126', plain,
% 0.46/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['124', '125'])).
% 0.46/0.66  thf('127', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('128', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66         (k1_tarski @ sk_A)) = (sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '126', '127'])).
% 0.46/0.66  thf('129', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66         (k1_tarski @ sk_A)) != (sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('130', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
