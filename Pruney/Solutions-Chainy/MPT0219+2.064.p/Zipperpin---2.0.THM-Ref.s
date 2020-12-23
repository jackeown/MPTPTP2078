%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EqhB23c5Hd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:12 EST 2020

% Result     : Theorem 3.16s
% Output     : Refutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  165 (1254 expanded)
%              Number of leaves         :   30 ( 430 expanded)
%              Depth                    :   23
%              Number of atoms          : 1324 (9902 expanded)
%              Number of equality atoms :  155 (1246 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['35','52'])).

thf('54',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','53'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('55',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_tarski @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('59',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X45 @ X45 @ X46 @ X47 )
      = ( k1_enumset1 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('84',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('104',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('105',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('106',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('108',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_tarski @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('109',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('116',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['54','65','66','69','92','102','103','104','113','114','115'])).

thf('117',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X45 @ X45 @ X46 @ X47 )
      = ( k1_enumset1 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k1_enumset1 @ sk_B @ sk_A @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['116','121'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('123',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('124',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['122','124'])).

thf('126',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('127',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['125','127'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('129',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('130',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['128','130'])).

thf('132',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EqhB23c5Hd
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.16/3.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.16/3.35  % Solved by: fo/fo7.sh
% 3.16/3.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.16/3.35  % done 2798 iterations in 2.921s
% 3.16/3.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.16/3.35  % SZS output start Refutation
% 3.16/3.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.16/3.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.16/3.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.16/3.35  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.16/3.35  thf(sk_A_type, type, sk_A: $i).
% 3.16/3.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.16/3.35  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.16/3.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.16/3.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.16/3.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.16/3.35  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.16/3.35  thf(sk_B_type, type, sk_B: $i).
% 3.16/3.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.16/3.35  thf(t100_xboole_1, axiom,
% 3.16/3.35    (![A:$i,B:$i]:
% 3.16/3.35     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.16/3.35  thf('0', plain,
% 3.16/3.35      (![X2 : $i, X3 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X2 @ X3)
% 3.16/3.35           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.16/3.35  thf(t21_xboole_1, axiom,
% 3.16/3.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.16/3.35  thf('1', plain,
% 3.16/3.35      (![X4 : $i, X5 : $i]:
% 3.16/3.35         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 3.16/3.35      inference('cnf', [status(esa)], [t21_xboole_1])).
% 3.16/3.35  thf('2', plain,
% 3.16/3.35      (![X2 : $i, X3 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X2 @ X3)
% 3.16/3.35           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.16/3.35  thf('3', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 3.16/3.35           = (k5_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['1', '2'])).
% 3.16/3.35  thf(t46_xboole_1, axiom,
% 3.16/3.35    (![A:$i,B:$i]:
% 3.16/3.35     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.16/3.35  thf('4', plain,
% 3.16/3.35      (![X6 : $i, X7 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 3.16/3.35      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.16/3.35  thf('5', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['3', '4'])).
% 3.16/3.35  thf(t91_xboole_1, axiom,
% 3.16/3.35    (![A:$i,B:$i,C:$i]:
% 3.16/3.35     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.16/3.35       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.16/3.35  thf('6', plain,
% 3.16/3.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 3.16/3.35           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.16/3.35  thf('7', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['5', '6'])).
% 3.16/3.35  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['3', '4'])).
% 3.16/3.35  thf('9', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['5', '6'])).
% 3.16/3.35  thf('10', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['8', '9'])).
% 3.16/3.35  thf(t5_boole, axiom,
% 3.16/3.35    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.16/3.35  thf('11', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.16/3.35      inference('cnf', [status(esa)], [t5_boole])).
% 3.16/3.35  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['10', '11'])).
% 3.16/3.35  thf('13', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('14', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k3_xboole_0 @ X1 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['0', '13'])).
% 3.16/3.35  thf(t98_xboole_1, axiom,
% 3.16/3.35    (![A:$i,B:$i]:
% 3.16/3.35     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.16/3.35  thf('15', plain,
% 3.16/3.35      (![X12 : $i, X13 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X12 @ X13)
% 3.16/3.35           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.16/3.35  thf('16', plain,
% 3.16/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['14', '15'])).
% 3.16/3.35  thf('17', plain,
% 3.16/3.35      (![X4 : $i, X5 : $i]:
% 3.16/3.35         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 3.16/3.35      inference('cnf', [status(esa)], [t21_xboole_1])).
% 3.16/3.35  thf(commutativity_k3_xboole_0, axiom,
% 3.16/3.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.16/3.35  thf('18', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.16/3.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.16/3.35  thf('19', plain,
% 3.16/3.35      (![X2 : $i, X3 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X2 @ X3)
% 3.16/3.35           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.16/3.35  thf('20', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X0 @ X1)
% 3.16/3.35           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['18', '19'])).
% 3.16/3.35  thf('21', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 3.16/3.35           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['17', '20'])).
% 3.16/3.35  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['3', '4'])).
% 3.16/3.35  thf('23', plain,
% 3.16/3.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 3.16/3.35           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.16/3.35  thf('24', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k1_xboole_0)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 3.16/3.35      inference('sup+', [status(thm)], ['22', '23'])).
% 3.16/3.35  thf('25', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('26', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['24', '25'])).
% 3.16/3.35  thf('27', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.16/3.35      inference('cnf', [status(esa)], [t5_boole])).
% 3.16/3.35  thf('28', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.16/3.35      inference('demod', [status(thm)], ['26', '27'])).
% 3.16/3.35  thf('29', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 3.16/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.16/3.35      inference('sup+', [status(thm)], ['21', '28'])).
% 3.16/3.35  thf('30', plain,
% 3.16/3.35      (![X12 : $i, X13 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X12 @ X13)
% 3.16/3.35           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.16/3.35  thf('31', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 3.16/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.16/3.35      inference('demod', [status(thm)], ['29', '30'])).
% 3.16/3.35  thf('32', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 3.16/3.35           = (k2_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['16', '31'])).
% 3.16/3.35  thf('33', plain,
% 3.16/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['14', '15'])).
% 3.16/3.35  thf('34', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 3.16/3.35           = (k3_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['32', '33'])).
% 3.16/3.35  thf('35', plain,
% 3.16/3.35      (![X12 : $i, X13 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X12 @ X13)
% 3.16/3.35           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.16/3.35  thf('36', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf(t13_zfmisc_1, conjecture,
% 3.16/3.35    (![A:$i,B:$i]:
% 3.16/3.35     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 3.16/3.35         ( k1_tarski @ A ) ) =>
% 3.16/3.35       ( ( A ) = ( B ) ) ))).
% 3.16/3.35  thf(zf_stmt_0, negated_conjecture,
% 3.16/3.35    (~( ![A:$i,B:$i]:
% 3.16/3.35        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 3.16/3.35            ( k1_tarski @ A ) ) =>
% 3.16/3.35          ( ( A ) = ( B ) ) ) )),
% 3.16/3.35    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 3.16/3.35  thf('37', plain,
% 3.16/3.35      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 3.16/3.35         = (k1_tarski @ sk_A))),
% 3.16/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.35  thf('38', plain,
% 3.16/3.35      (![X12 : $i, X13 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X12 @ X13)
% 3.16/3.35           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.16/3.35  thf('39', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('40', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X0 @ X1)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['38', '39'])).
% 3.16/3.35  thf('41', plain,
% 3.16/3.35      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 3.16/3.35         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['37', '40'])).
% 3.16/3.35  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['3', '4'])).
% 3.16/3.35  thf('43', plain,
% 3.16/3.35      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 3.16/3.35      inference('demod', [status(thm)], ['41', '42'])).
% 3.16/3.35  thf('44', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k3_xboole_0 @ X1 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['0', '13'])).
% 3.16/3.35  thf('45', plain,
% 3.16/3.35      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 3.16/3.35         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['43', '44'])).
% 3.16/3.35  thf('46', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.16/3.35      inference('cnf', [status(esa)], [t5_boole])).
% 3.16/3.35  thf('47', plain,
% 3.16/3.35      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 3.16/3.35         = (k1_tarski @ sk_B))),
% 3.16/3.35      inference('demod', [status(thm)], ['45', '46'])).
% 3.16/3.35  thf('48', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X0 @ X1)
% 3.16/3.35           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['18', '19'])).
% 3.16/3.35  thf('49', plain,
% 3.16/3.35      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 3.16/3.35         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['47', '48'])).
% 3.16/3.35  thf('50', plain,
% 3.16/3.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 3.16/3.35           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.16/3.35  thf('51', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ 
% 3.16/3.35           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 3.16/3.35           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 3.16/3.35              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['49', '50'])).
% 3.16/3.35  thf('52', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ 
% 3.16/3.35           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 3.16/3.35           (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 3.16/3.35           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['36', '51'])).
% 3.16/3.35  thf('53', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ 
% 3.16/3.35           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 3.16/3.35           (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 3.16/3.35           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 3.16/3.35              (k4_xboole_0 @ X0 @ (k1_tarski @ sk_B))))),
% 3.16/3.35      inference('sup+', [status(thm)], ['35', '52'])).
% 3.16/3.35  thf('54', plain,
% 3.16/3.35      (((k5_xboole_0 @ 
% 3.16/3.35         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 3.16/3.35         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 3.16/3.35         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 3.16/3.35            (k4_xboole_0 @ 
% 3.16/3.35             (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)) @ 
% 3.16/3.35             (k1_tarski @ sk_B))))),
% 3.16/3.35      inference('sup+', [status(thm)], ['34', '53'])).
% 3.16/3.35  thf(t69_enumset1, axiom,
% 3.16/3.35    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.16/3.35  thf('55', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf('56', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf(l53_enumset1, axiom,
% 3.16/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.16/3.35     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.16/3.35       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.16/3.35  thf('57', plain,
% 3.16/3.35      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 3.16/3.35           = (k2_xboole_0 @ (k2_tarski @ X31 @ X32) @ (k2_tarski @ X33 @ X34)))),
% 3.16/3.35      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.16/3.35  thf('58', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 3.16/3.35           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['56', '57'])).
% 3.16/3.35  thf(t71_enumset1, axiom,
% 3.16/3.35    (![A:$i,B:$i,C:$i]:
% 3.16/3.35     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.16/3.35  thf('59', plain,
% 3.16/3.35      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X45 @ X45 @ X46 @ X47)
% 3.16/3.35           = (k1_enumset1 @ X45 @ X46 @ X47))),
% 3.16/3.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.16/3.35  thf(t70_enumset1, axiom,
% 3.16/3.35    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.16/3.35  thf('60', plain,
% 3.16/3.35      (![X43 : $i, X44 : $i]:
% 3.16/3.35         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 3.16/3.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.16/3.35  thf('61', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['59', '60'])).
% 3.16/3.35  thf('62', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 3.16/3.35           = (k2_tarski @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['58', '61'])).
% 3.16/3.35  thf('63', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 3.16/3.35           = (k2_tarski @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['55', '62'])).
% 3.16/3.35  thf('64', plain,
% 3.16/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['14', '15'])).
% 3.16/3.35  thf('65', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 3.16/3.35           = (k2_tarski @ X0 @ X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['63', '64'])).
% 3.16/3.35  thf('66', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf('67', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.16/3.35      inference('demod', [status(thm)], ['26', '27'])).
% 3.16/3.35  thf('68', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('69', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.16/3.35  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['3', '4'])).
% 3.16/3.35  thf('71', plain,
% 3.16/3.35      (![X2 : $i, X3 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X2 @ X3)
% 3.16/3.35           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.16/3.35  thf('72', plain,
% 3.16/3.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 3.16/3.35           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.16/3.35  thf('73', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['71', '72'])).
% 3.16/3.35  thf('74', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['70', '73'])).
% 3.16/3.35  thf('75', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.16/3.35      inference('cnf', [status(esa)], [t5_boole])).
% 3.16/3.35  thf('76', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (X1))),
% 3.16/3.35      inference('demod', [status(thm)], ['74', '75'])).
% 3.16/3.35  thf('77', plain,
% 3.16/3.35      (![X12 : $i, X13 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X12 @ X13)
% 3.16/3.35           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.16/3.35  thf('78', plain,
% 3.16/3.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 3.16/3.35           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.16/3.35  thf('79', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['77', '78'])).
% 3.16/3.35  thf('80', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 3.16/3.35           = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['76', '79'])).
% 3.16/3.35  thf('81', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.16/3.35  thf('82', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['80', '81'])).
% 3.16/3.35  thf('83', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X0 @ X1)
% 3.16/3.35           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['18', '19'])).
% 3.16/3.35  thf('84', plain,
% 3.16/3.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 3.16/3.35           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.16/3.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.16/3.35  thf('85', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['83', '84'])).
% 3.16/3.35  thf('86', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['82', '85'])).
% 3.16/3.35  thf('87', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('88', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['86', '87'])).
% 3.16/3.35  thf('89', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('90', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X1 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['88', '89'])).
% 3.16/3.35  thf('91', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.16/3.35  thf('92', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X1 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['90', '91'])).
% 3.16/3.35  thf('93', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['86', '87'])).
% 3.16/3.35  thf('94', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.16/3.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['77', '78'])).
% 3.16/3.35  thf('95', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (k5_xboole_0 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['93', '94'])).
% 3.16/3.35  thf('96', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['3', '4'])).
% 3.16/3.35  thf('97', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.16/3.35           = (k1_xboole_0))),
% 3.16/3.35      inference('demod', [status(thm)], ['95', '96'])).
% 3.16/3.35  thf('98', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.16/3.35      inference('demod', [status(thm)], ['7', '12'])).
% 3.16/3.35  thf('99', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ X1 @ X0)
% 3.16/3.35           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['97', '98'])).
% 3.16/3.35  thf('100', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.16/3.35  thf('101', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['10', '11'])).
% 3.16/3.35  thf('102', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.16/3.35      inference('demod', [status(thm)], ['99', '100', '101'])).
% 3.16/3.35  thf('103', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 3.16/3.35           = (k2_tarski @ X0 @ X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['63', '64'])).
% 3.16/3.35  thf('104', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf('105', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf('106', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf('107', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['59', '60'])).
% 3.16/3.35  thf('108', plain,
% 3.16/3.35      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 3.16/3.35           = (k2_xboole_0 @ (k2_tarski @ X31 @ X32) @ (k2_tarski @ X33 @ X34)))),
% 3.16/3.35      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.16/3.35  thf('109', plain,
% 3.16/3.35      (![X6 : $i, X7 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 3.16/3.35      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.16/3.35  thf('110', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 3.16/3.35           (k2_enumset1 @ X3 @ X2 @ X1 @ X0)) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['108', '109'])).
% 3.16/3.35  thf('111', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))
% 3.16/3.35           = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['107', '110'])).
% 3.16/3.35  thf('112', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 3.16/3.35           = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['106', '111'])).
% 3.16/3.35  thf('113', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['105', '112'])).
% 3.16/3.35  thf('114', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.16/3.35  thf('115', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.16/3.35      inference('demod', [status(thm)], ['10', '11'])).
% 3.16/3.35  thf('116', plain,
% 3.16/3.35      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 3.16/3.35         = (k1_tarski @ sk_A))),
% 3.16/3.35      inference('demod', [status(thm)],
% 3.16/3.35                ['54', '65', '66', '69', '92', '102', '103', '104', '113', 
% 3.16/3.35                 '114', '115'])).
% 3.16/3.35  thf('117', plain,
% 3.16/3.35      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.16/3.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.16/3.35  thf('118', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 3.16/3.35           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['56', '57'])).
% 3.16/3.35  thf('119', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0)
% 3.16/3.35           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 3.16/3.35      inference('sup+', [status(thm)], ['117', '118'])).
% 3.16/3.35  thf('120', plain,
% 3.16/3.35      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.16/3.35         ((k2_enumset1 @ X45 @ X45 @ X46 @ X47)
% 3.16/3.35           = (k1_enumset1 @ X45 @ X46 @ X47))),
% 3.16/3.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.16/3.35  thf('121', plain,
% 3.16/3.35      (![X0 : $i, X1 : $i]:
% 3.16/3.35         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.16/3.35           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 3.16/3.35      inference('sup+', [status(thm)], ['119', '120'])).
% 3.16/3.35  thf('122', plain,
% 3.16/3.35      (((k1_enumset1 @ sk_B @ sk_A @ sk_A) = (k1_tarski @ sk_A))),
% 3.16/3.35      inference('demod', [status(thm)], ['116', '121'])).
% 3.16/3.35  thf(d1_enumset1, axiom,
% 3.16/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.16/3.35     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.16/3.35       ( ![E:$i]:
% 3.16/3.35         ( ( r2_hidden @ E @ D ) <=>
% 3.16/3.35           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 3.16/3.35  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.16/3.35  thf(zf_stmt_2, axiom,
% 3.16/3.35    (![E:$i,C:$i,B:$i,A:$i]:
% 3.16/3.35     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 3.16/3.35       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 3.16/3.35  thf(zf_stmt_3, axiom,
% 3.16/3.35    (![A:$i,B:$i,C:$i,D:$i]:
% 3.16/3.35     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.16/3.35       ( ![E:$i]:
% 3.16/3.35         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 3.16/3.35  thf('123', plain,
% 3.16/3.35      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.16/3.35         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 3.16/3.35          | (r2_hidden @ X19 @ X23)
% 3.16/3.35          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 3.16/3.35      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.16/3.35  thf('124', plain,
% 3.16/3.35      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.16/3.35         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 3.16/3.35          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 3.16/3.35      inference('simplify', [status(thm)], ['123'])).
% 3.16/3.35  thf('125', plain,
% 3.16/3.35      (![X0 : $i]:
% 3.16/3.35         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 3.16/3.35          | (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_B))),
% 3.16/3.35      inference('sup+', [status(thm)], ['122', '124'])).
% 3.16/3.35  thf('126', plain,
% 3.16/3.35      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 3.16/3.35         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 3.16/3.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.16/3.35  thf('127', plain,
% 3.16/3.35      (![X14 : $i, X16 : $i, X17 : $i]:
% 3.16/3.35         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 3.16/3.35      inference('simplify', [status(thm)], ['126'])).
% 3.16/3.35  thf('128', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 3.16/3.35      inference('sup-', [status(thm)], ['125', '127'])).
% 3.16/3.35  thf(d1_tarski, axiom,
% 3.16/3.35    (![A:$i,B:$i]:
% 3.16/3.35     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.16/3.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.16/3.35  thf('129', plain,
% 3.16/3.35      (![X26 : $i, X28 : $i, X29 : $i]:
% 3.16/3.35         (~ (r2_hidden @ X29 @ X28)
% 3.16/3.35          | ((X29) = (X26))
% 3.16/3.35          | ((X28) != (k1_tarski @ X26)))),
% 3.16/3.35      inference('cnf', [status(esa)], [d1_tarski])).
% 3.16/3.35  thf('130', plain,
% 3.16/3.35      (![X26 : $i, X29 : $i]:
% 3.16/3.35         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 3.16/3.35      inference('simplify', [status(thm)], ['129'])).
% 3.16/3.35  thf('131', plain, (((sk_B) = (sk_A))),
% 3.16/3.35      inference('sup-', [status(thm)], ['128', '130'])).
% 3.16/3.35  thf('132', plain, (((sk_A) != (sk_B))),
% 3.16/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.35  thf('133', plain, ($false),
% 3.16/3.35      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 3.16/3.35  
% 3.16/3.35  % SZS output end Refutation
% 3.16/3.35  
% 3.16/3.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
