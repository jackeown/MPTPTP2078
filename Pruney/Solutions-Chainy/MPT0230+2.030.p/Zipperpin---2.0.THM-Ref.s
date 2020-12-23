%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IP1aI1Yf1r

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:14 EST 2020

% Result     : Theorem 3.94s
% Output     : Refutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 159 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  926 (1289 expanded)
%              Number of equality atoms :  110 ( 152 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_tarski @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['27','30'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_tarski @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('40',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X38 @ X39 @ X40 ) @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('45',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ( k1_enumset1 @ X70 @ X72 @ X71 )
      = ( k1_enumset1 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('46',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X36 @ X35 ) @ ( k2_tarski @ X37 @ X35 ) )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_tarski @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('50',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X36 @ X35 @ X37 @ X35 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','53'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('55',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X45 @ X45 @ X46 @ X47 )
      = ( k1_enumset1 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('56',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('64',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X45 @ X45 @ X46 @ X47 )
      = ( k1_enumset1 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','66'])).

thf('68',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ( k1_enumset1 @ X70 @ X72 @ X71 )
      = ( k1_enumset1 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('69',plain,
    ( ( k1_enumset1 @ sk_C @ sk_A @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['31','67','68'])).

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

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['69','71'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('73',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X27 )
      | ( X29 = X28 )
      | ( X29 = X25 )
      | ( X27
       != ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('74',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( X29 = X25 )
      | ( X29 = X28 )
      | ~ ( r2_hidden @ X29 @ ( k2_tarski @ X28 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_C )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IP1aI1Yf1r
% 0.14/0.37  % Computer   : n022.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:26:56 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 3.94/4.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.94/4.15  % Solved by: fo/fo7.sh
% 3.94/4.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.94/4.15  % done 5358 iterations in 3.663s
% 3.94/4.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.94/4.15  % SZS output start Refutation
% 3.94/4.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.94/4.15  thf(sk_C_type, type, sk_C: $i).
% 3.94/4.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.94/4.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.94/4.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.94/4.15  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.94/4.15  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.94/4.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.94/4.15  thf(sk_B_type, type, sk_B: $i).
% 3.94/4.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.94/4.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.94/4.15  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.94/4.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.94/4.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.94/4.15  thf(sk_A_type, type, sk_A: $i).
% 3.94/4.15  thf(t25_zfmisc_1, conjecture,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 3.94/4.15          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 3.94/4.15  thf(zf_stmt_0, negated_conjecture,
% 3.94/4.15    (~( ![A:$i,B:$i,C:$i]:
% 3.94/4.15        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 3.94/4.15             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 3.94/4.15    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 3.94/4.15  thf('0', plain,
% 3.94/4.15      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf(t28_xboole_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.94/4.15  thf('1', plain,
% 3.94/4.15      (![X5 : $i, X6 : $i]:
% 3.94/4.15         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 3.94/4.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.94/4.15  thf('2', plain,
% 3.94/4.15      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 3.94/4.15         = (k1_tarski @ sk_A))),
% 3.94/4.15      inference('sup-', [status(thm)], ['0', '1'])).
% 3.94/4.15  thf(t100_xboole_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.94/4.15  thf('3', plain,
% 3.94/4.15      (![X3 : $i, X4 : $i]:
% 3.94/4.15         ((k4_xboole_0 @ X3 @ X4)
% 3.94/4.15           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.94/4.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.94/4.15  thf('4', plain,
% 3.94/4.15      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 3.94/4.15         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['2', '3'])).
% 3.94/4.15  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.94/4.15  thf('5', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.94/4.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.94/4.15  thf('6', plain,
% 3.94/4.15      (![X5 : $i, X6 : $i]:
% 3.94/4.15         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 3.94/4.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.94/4.15  thf('7', plain,
% 3.94/4.15      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.94/4.15      inference('sup-', [status(thm)], ['5', '6'])).
% 3.94/4.15  thf(commutativity_k3_xboole_0, axiom,
% 3.94/4.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.94/4.15  thf('8', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.94/4.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.94/4.15  thf('9', plain,
% 3.94/4.15      (![X3 : $i, X4 : $i]:
% 3.94/4.15         ((k4_xboole_0 @ X3 @ X4)
% 3.94/4.15           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.94/4.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.94/4.15  thf('10', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k4_xboole_0 @ X0 @ X1)
% 3.94/4.15           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['8', '9'])).
% 3.94/4.15  thf('11', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['7', '10'])).
% 3.94/4.15  thf(t5_boole, axiom,
% 3.94/4.15    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.94/4.15  thf('12', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 3.94/4.15      inference('cnf', [status(esa)], [t5_boole])).
% 3.94/4.15  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.94/4.15      inference('demod', [status(thm)], ['11', '12'])).
% 3.94/4.15  thf(t48_xboole_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.94/4.15  thf('14', plain,
% 3.94/4.15      (![X8 : $i, X9 : $i]:
% 3.94/4.15         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 3.94/4.15           = (k3_xboole_0 @ X8 @ X9))),
% 3.94/4.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.94/4.15  thf('15', plain,
% 3.94/4.15      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['13', '14'])).
% 3.94/4.15  thf(idempotence_k3_xboole_0, axiom,
% 3.94/4.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.94/4.15  thf('16', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.94/4.15      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.94/4.15  thf('17', plain,
% 3.94/4.15      (![X3 : $i, X4 : $i]:
% 3.94/4.15         ((k4_xboole_0 @ X3 @ X4)
% 3.94/4.15           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.94/4.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.94/4.15  thf('18', plain,
% 3.94/4.15      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['16', '17'])).
% 3.94/4.15  thf('19', plain,
% 3.94/4.15      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.94/4.15      inference('sup-', [status(thm)], ['5', '6'])).
% 3.94/4.15  thf('20', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.94/4.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.94/4.15  thf('21', plain,
% 3.94/4.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['19', '20'])).
% 3.94/4.15  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.94/4.15      inference('demod', [status(thm)], ['15', '18', '21'])).
% 3.94/4.15  thf('23', plain,
% 3.94/4.15      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 3.94/4.15         = (k1_xboole_0))),
% 3.94/4.15      inference('demod', [status(thm)], ['4', '22'])).
% 3.94/4.15  thf(t98_xboole_1, axiom,
% 3.94/4.15    (![A:$i,B:$i]:
% 3.94/4.15     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.94/4.15  thf('24', plain,
% 3.94/4.15      (![X11 : $i, X12 : $i]:
% 3.94/4.15         ((k2_xboole_0 @ X11 @ X12)
% 3.94/4.15           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 3.94/4.15      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.94/4.15  thf('25', plain,
% 3.94/4.15      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 3.94/4.15         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['23', '24'])).
% 3.94/4.15  thf('26', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 3.94/4.15      inference('cnf', [status(esa)], [t5_boole])).
% 3.94/4.15  thf('27', plain,
% 3.94/4.15      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 3.94/4.15         = (k2_tarski @ sk_B @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['25', '26'])).
% 3.94/4.15  thf(t69_enumset1, axiom,
% 3.94/4.15    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.94/4.15  thf('28', plain,
% 3.94/4.15      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.94/4.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.94/4.15  thf(l53_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i]:
% 3.94/4.15     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.94/4.15       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.94/4.15  thf('29', plain,
% 3.94/4.15      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X31 @ X32) @ (k2_tarski @ X33 @ X34)))),
% 3.94/4.15      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.94/4.15  thf('30', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['28', '29'])).
% 3.94/4.15  thf('31', plain,
% 3.94/4.15      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['27', '30'])).
% 3.94/4.15  thf(t70_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.94/4.15  thf('32', plain,
% 3.94/4.15      (![X43 : $i, X44 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 3.94/4.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.94/4.15  thf('33', plain,
% 3.94/4.15      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.94/4.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.94/4.15  thf('34', plain,
% 3.94/4.15      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['32', '33'])).
% 3.94/4.15  thf('35', plain,
% 3.94/4.15      (![X43 : $i, X44 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 3.94/4.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.94/4.15  thf('36', plain,
% 3.94/4.15      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X31 @ X32) @ (k2_tarski @ X33 @ X34)))),
% 3.94/4.15      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.94/4.15  thf('37', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 3.94/4.15              (k1_enumset1 @ X1 @ X1 @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['35', '36'])).
% 3.94/4.15  thf('38', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['34', '37'])).
% 3.94/4.15  thf('39', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['28', '29'])).
% 3.94/4.15  thf('40', plain,
% 3.94/4.15      (![X43 : $i, X44 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 3.94/4.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.94/4.15  thf(t46_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i]:
% 3.94/4.15     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.94/4.15       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.94/4.15  thf('41', plain,
% 3.94/4.15      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X38 @ X39 @ X40 @ X41)
% 3.94/4.15           = (k2_xboole_0 @ (k1_enumset1 @ X38 @ X39 @ X40) @ (k1_tarski @ X41)))),
% 3.94/4.15      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.94/4.15  thf('42', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['40', '41'])).
% 3.94/4.15  thf('43', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['39', '42'])).
% 3.94/4.15  thf('44', plain,
% 3.94/4.15      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.94/4.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.94/4.15  thf(t98_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 3.94/4.15  thf('45', plain,
% 3.94/4.15      (![X70 : $i, X71 : $i, X72 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X70 @ X72 @ X71) = (k1_enumset1 @ X70 @ X71 @ X72))),
% 3.94/4.15      inference('cnf', [status(esa)], [t98_enumset1])).
% 3.94/4.15  thf('46', plain,
% 3.94/4.15      (![X43 : $i, X44 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 3.94/4.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.94/4.15  thf('47', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.94/4.15      inference('sup+', [status(thm)], ['45', '46'])).
% 3.94/4.15  thf(t137_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.94/4.15       ( k1_enumset1 @ A @ B @ C ) ))).
% 3.94/4.15  thf('48', plain,
% 3.94/4.15      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.94/4.15         ((k2_xboole_0 @ (k2_tarski @ X36 @ X35) @ (k2_tarski @ X37 @ X35))
% 3.94/4.15           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 3.94/4.15      inference('cnf', [status(esa)], [t137_enumset1])).
% 3.94/4.15  thf('49', plain,
% 3.94/4.15      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X31 @ X32 @ X33 @ X34)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X31 @ X32) @ (k2_tarski @ X33 @ X34)))),
% 3.94/4.15      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.94/4.15  thf('50', plain,
% 3.94/4.15      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X36 @ X35 @ X37 @ X35)
% 3.94/4.15           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 3.94/4.15      inference('demod', [status(thm)], ['48', '49'])).
% 3.94/4.15  thf('51', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X0 @ X1 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['47', '50'])).
% 3.94/4.15  thf('52', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['28', '29'])).
% 3.94/4.15  thf('53', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_tarski @ X1 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X1)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['51', '52'])).
% 3.94/4.15  thf('54', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.94/4.15           = (k2_tarski @ X0 @ X1))),
% 3.94/4.15      inference('demod', [status(thm)], ['43', '44', '53'])).
% 3.94/4.15  thf(t71_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.94/4.15  thf('55', plain,
% 3.94/4.15      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X45 @ X45 @ X46 @ X47)
% 3.94/4.15           = (k1_enumset1 @ X45 @ X46 @ X47))),
% 3.94/4.15      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.94/4.15  thf('56', plain,
% 3.94/4.15      (![X43 : $i, X44 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 3.94/4.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.94/4.15  thf('57', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['55', '56'])).
% 3.94/4.15  thf('58', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['40', '41'])).
% 3.94/4.15  thf('59', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_tarski @ X1 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['57', '58'])).
% 3.94/4.15  thf('60', plain,
% 3.94/4.15      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 3.94/4.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.94/4.15  thf('61', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]:
% 3.94/4.15         ((k2_tarski @ X1 @ X0)
% 3.94/4.15           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 3.94/4.15      inference('demod', [status(thm)], ['59', '60'])).
% 3.94/4.15  thf('62', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['54', '61'])).
% 3.94/4.15  thf('63', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.94/4.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.94/4.15      inference('sup+', [status(thm)], ['40', '41'])).
% 3.94/4.15  thf('64', plain,
% 3.94/4.15      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X45 @ X45 @ X46 @ X47)
% 3.94/4.15           = (k1_enumset1 @ X45 @ X46 @ X47))),
% 3.94/4.15      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.94/4.15  thf('65', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 3.94/4.15           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.94/4.15      inference('sup+', [status(thm)], ['63', '64'])).
% 3.94/4.15  thf('66', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 3.94/4.15           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.94/4.15      inference('sup+', [status(thm)], ['62', '65'])).
% 3.94/4.15  thf('67', plain,
% 3.94/4.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.94/4.15         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 3.94/4.15      inference('demod', [status(thm)], ['38', '66'])).
% 3.94/4.15  thf('68', plain,
% 3.94/4.15      (![X70 : $i, X71 : $i, X72 : $i]:
% 3.94/4.15         ((k1_enumset1 @ X70 @ X72 @ X71) = (k1_enumset1 @ X70 @ X71 @ X72))),
% 3.94/4.15      inference('cnf', [status(esa)], [t98_enumset1])).
% 3.94/4.15  thf('69', plain,
% 3.94/4.15      (((k1_enumset1 @ sk_C @ sk_A @ sk_B) = (k2_tarski @ sk_B @ sk_C))),
% 3.94/4.15      inference('demod', [status(thm)], ['31', '67', '68'])).
% 3.94/4.15  thf(d1_enumset1, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i]:
% 3.94/4.15     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.94/4.15       ( ![E:$i]:
% 3.94/4.15         ( ( r2_hidden @ E @ D ) <=>
% 3.94/4.15           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 3.94/4.15  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.94/4.15  thf(zf_stmt_2, axiom,
% 3.94/4.15    (![E:$i,C:$i,B:$i,A:$i]:
% 3.94/4.15     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 3.94/4.15       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 3.94/4.15  thf(zf_stmt_3, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i,D:$i]:
% 3.94/4.15     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.94/4.15       ( ![E:$i]:
% 3.94/4.15         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 3.94/4.15  thf('70', plain,
% 3.94/4.15      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 3.94/4.15         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 3.94/4.15          | (r2_hidden @ X18 @ X22)
% 3.94/4.15          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.94/4.15  thf('71', plain,
% 3.94/4.15      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 3.94/4.15         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 3.94/4.15          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 3.94/4.15      inference('simplify', [status(thm)], ['70'])).
% 3.94/4.15  thf('72', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 3.94/4.15          | (zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_C))),
% 3.94/4.15      inference('sup+', [status(thm)], ['69', '71'])).
% 3.94/4.15  thf(d2_tarski, axiom,
% 3.94/4.15    (![A:$i,B:$i,C:$i]:
% 3.94/4.15     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 3.94/4.15       ( ![D:$i]:
% 3.94/4.15         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 3.94/4.15  thf('73', plain,
% 3.94/4.15      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.94/4.15         (~ (r2_hidden @ X29 @ X27)
% 3.94/4.15          | ((X29) = (X28))
% 3.94/4.15          | ((X29) = (X25))
% 3.94/4.15          | ((X27) != (k2_tarski @ X28 @ X25)))),
% 3.94/4.15      inference('cnf', [status(esa)], [d2_tarski])).
% 3.94/4.15  thf('74', plain,
% 3.94/4.15      (![X25 : $i, X28 : $i, X29 : $i]:
% 3.94/4.15         (((X29) = (X25))
% 3.94/4.15          | ((X29) = (X28))
% 3.94/4.15          | ~ (r2_hidden @ X29 @ (k2_tarski @ X28 @ X25)))),
% 3.94/4.15      inference('simplify', [status(thm)], ['73'])).
% 3.94/4.15  thf('75', plain,
% 3.94/4.15      (![X0 : $i]:
% 3.94/4.15         ((zip_tseitin_0 @ X0 @ sk_B @ sk_A @ sk_C)
% 3.94/4.15          | ((X0) = (sk_B))
% 3.94/4.15          | ((X0) = (sk_C)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['72', '74'])).
% 3.94/4.15  thf('76', plain,
% 3.94/4.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 3.94/4.15         (((X14) != (X16)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.94/4.15  thf('77', plain,
% 3.94/4.15      (![X13 : $i, X15 : $i, X16 : $i]:
% 3.94/4.15         ~ (zip_tseitin_0 @ X16 @ X15 @ X16 @ X13)),
% 3.94/4.15      inference('simplify', [status(thm)], ['76'])).
% 3.94/4.15  thf('78', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 3.94/4.15      inference('sup-', [status(thm)], ['75', '77'])).
% 3.94/4.15  thf('79', plain, (((sk_A) != (sk_B))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('80', plain, (((sk_A) != (sk_C))),
% 3.94/4.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.94/4.15  thf('81', plain, ($false),
% 3.94/4.15      inference('simplify_reflect-', [status(thm)], ['78', '79', '80'])).
% 3.94/4.15  
% 3.94/4.15  % SZS output end Refutation
% 3.94/4.15  
% 3.94/4.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
