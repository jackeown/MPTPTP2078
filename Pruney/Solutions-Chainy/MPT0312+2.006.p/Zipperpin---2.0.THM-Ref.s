%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z95RlNEkcc

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 215 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  711 (1661 expanded)
%              Number of equality atoms :   85 ( 200 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X42 @ X44 ) @ ( k3_xboole_0 @ X43 @ X45 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X42 @ X43 ) @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['5','6'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_D @ sk_C ) @ sk_D ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_D @ ( k5_xboole_0 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','24'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('41',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_A @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_A @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['63','64','65','72','73'])).

thf('75',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['28','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z95RlNEkcc
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 164 iterations in 0.107s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(t124_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.57       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.21/0.57         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.57          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.21/0.57            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.21/0.57         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t123_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.57       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.57         ((k2_zfmisc_1 @ (k3_xboole_0 @ X42 @ X44) @ (k3_xboole_0 @ X43 @ X45))
% 0.21/0.57           = (k3_xboole_0 @ (k2_zfmisc_1 @ X42 @ X43) @ 
% 0.21/0.57              (k2_zfmisc_1 @ X44 @ X45)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.57  thf(t92_xboole_1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('2', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.57  thf('3', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t12_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.57  thf('5', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.57  thf('7', plain, (((k2_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 0.21/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.57  thf(t95_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k3_xboole_0 @ A @ B ) =
% 0.21/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ X12)
% 0.21/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.21/0.57              (k2_xboole_0 @ X11 @ X12)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.21/0.57         = (k5_xboole_0 @ (k5_xboole_0 @ sk_D @ sk_C) @ sk_D))),
% 0.21/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf(t91_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.21/0.57         = (k5_xboole_0 @ sk_D @ (k5_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('13', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.21/0.57           = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (((k5_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_C)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ sk_C @ 
% 0.21/0.57              (k5_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_C) @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf('18', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ X12)
% 0.21/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.21/0.57              (k2_xboole_0 @ X11 @ X12)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.57  thf('21', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.57  thf('22', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.57  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((X0)
% 0.21/0.57           = (k5_xboole_0 @ sk_C @ 
% 0.21/0.57              (k5_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_C) @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['17', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_D @ sk_C) = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['2', '24'])).
% 0.21/0.57  thf(t5_boole, axiom,
% 0.21/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.57  thf('26', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.57  thf('27', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.57         != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1', '27'])).
% 0.21/0.57  thf('29', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.57  thf('31', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.57  thf('33', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ X12)
% 0.21/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.21/0.57              (k2_xboole_0 @ X11 @ X12)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.21/0.57         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.21/0.57         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.21/0.57         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.21/0.57           = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ sk_A @ 
% 0.21/0.57              (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((X0)
% 0.21/0.57           = (k5_xboole_0 @ sk_A @ 
% 0.21/0.57              (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['38', '45'])).
% 0.21/0.57  thf('47', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.57  thf('48', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (((sk_A) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '48'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ sk_A @ X0)
% 0.21/0.57           = (k5_xboole_0 @ sk_B @ 
% 0.21/0.57              (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ sk_A @ X0)
% 0.21/0.57           = (k5_xboole_0 @ sk_B @ 
% 0.21/0.57              (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0))))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0))
% 0.21/0.57           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['53', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ X12)
% 0.21/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.21/0.57              (k2_xboole_0 @ X11 @ X12)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.57           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ X12)
% 0.21/0.57           = (k5_xboole_0 @ X11 @ 
% 0.21/0.57              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 0.21/0.57      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.21/0.57         = (k5_xboole_0 @ sk_B @ 
% 0.21/0.57            (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['59', '62'])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.57  thf('65', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.21/0.57           = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.21/0.57           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['66', '67'])).
% 0.21/0.57  thf('69', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.57  thf('74', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['63', '64', '65', '72', '73'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['28', '74'])).
% 0.21/0.57  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
