%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OyYhQRlAUU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:46 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  141 (1466 expanded)
%              Number of leaves         :   36 ( 524 expanded)
%              Depth                    :   21
%              Number of atoms          : 1036 (12337 expanded)
%              Number of equality atoms :  112 (1421 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21','24','25','26'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('63',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','61','64'])).

thf('66',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','61','64'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('67',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','78'])).

thf('80',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('81',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

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

thf('82',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X37 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X28 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('91',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['79','94'])).

thf('96',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','78'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('97',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('98',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('100',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['95','96','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OyYhQRlAUU
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:29:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 661 iterations in 0.231s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.68  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.50/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.50/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(t49_zfmisc_1, conjecture,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i,B:$i]:
% 0.50/0.68        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.50/0.68  thf('0', plain,
% 0.50/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(t94_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k2_xboole_0 @ A @ B ) =
% 0.50/0.68       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X26 @ X27)
% 0.50/0.68           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 0.50/0.68              (k3_xboole_0 @ X26 @ X27)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.50/0.68  thf(commutativity_k5_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.50/0.68  thf('2', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('3', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X26 @ X27)
% 0.50/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ 
% 0.50/0.68              (k5_xboole_0 @ X26 @ X27)))),
% 0.50/0.68      inference('demod', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf('4', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X26 @ X27)
% 0.50/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ 
% 0.50/0.68              (k5_xboole_0 @ X26 @ X27)))),
% 0.50/0.68      inference('demod', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf('5', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.50/0.68           = (k5_xboole_0 @ 
% 0.50/0.68              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.68              (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['3', '4'])).
% 0.50/0.68  thf('6', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('7', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.50/0.68           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.50/0.68              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.50/0.68      inference('demod', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf('8', plain,
% 0.50/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.50/0.68         (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.50/0.68         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.50/0.68            (k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.50/0.68             (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['0', '7'])).
% 0.50/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.68  thf('9', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('11', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('12', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('13', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf(t5_boole, axiom,
% 0.50/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.68  thf('14', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.50/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.68  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.50/0.68         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.50/0.68      inference('demod', [status(thm)], ['8', '9', '10', '11', '12', '15'])).
% 0.50/0.68  thf('17', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('18', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X26 @ X27)
% 0.50/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ 
% 0.50/0.68              (k5_xboole_0 @ X26 @ X27)))),
% 0.50/0.68      inference('demod', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf('19', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.68  thf('20', plain,
% 0.50/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.50/0.68         = (k5_xboole_0 @ 
% 0.50/0.68            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.50/0.68            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['16', '19'])).
% 0.50/0.68  thf(t91_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.68  thf('21', plain,
% 0.50/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.50/0.68           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.68  thf('22', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf(t100_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (![X14 : $i, X15 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X14 @ X15)
% 0.50/0.68           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('24', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.50/0.68  thf('25', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('26', plain,
% 0.50/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.50/0.68           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.68  thf('27', plain,
% 0.50/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.50/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.50/0.68            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.50/0.68             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.50/0.68      inference('demod', [status(thm)], ['20', '21', '24', '25', '26'])).
% 0.50/0.68  thf(t92_xboole_1, axiom,
% 0.50/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.50/0.68  thf('28', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.68  thf('29', plain,
% 0.50/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.50/0.68           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.68  thf('30', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['28', '29'])).
% 0.50/0.68  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.68  thf('32', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.50/0.68  thf('33', plain,
% 0.50/0.68      (((k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.50/0.68         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.50/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.50/0.68            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['27', '32'])).
% 0.50/0.68  thf('34', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('35', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.50/0.68  thf('36', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['34', '35'])).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.50/0.68         = (k5_xboole_0 @ 
% 0.50/0.68            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.50/0.68            (k5_xboole_0 @ sk_B @ 
% 0.50/0.68             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.50/0.68              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['33', '36'])).
% 0.50/0.68  thf('38', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['34', '35'])).
% 0.50/0.68  thf('39', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.68  thf(t36_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.50/0.68  thf('40', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 0.50/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.68  thf(t28_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.68  thf('41', plain,
% 0.50/0.68      (![X16 : $i, X17 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('42', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.50/0.68           = (k4_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('44', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.50/0.68           = (k4_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.50/0.68  thf('45', plain,
% 0.50/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.50/0.68         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['39', '44'])).
% 0.50/0.68  thf('46', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('47', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.68  thf('48', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.50/0.68  thf('49', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.50/0.68  thf('50', plain,
% 0.50/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.50/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.50/0.68  thf('51', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.68  thf('52', plain,
% 0.50/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.50/0.68  thf('53', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.50/0.68      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.50/0.68  thf('54', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.50/0.68  thf('55', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['53', '54'])).
% 0.50/0.68  thf(d10_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.68  thf('56', plain,
% 0.50/0.68      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.68  thf('57', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 0.50/0.68      inference('simplify', [status(thm)], ['56'])).
% 0.50/0.68  thf('58', plain,
% 0.50/0.68      (![X16 : $i, X17 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.50/0.68  thf('60', plain,
% 0.50/0.68      (![X14 : $i, X15 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X14 @ X15)
% 0.50/0.68           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('61', plain,
% 0.50/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.68  thf('62', plain,
% 0.50/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.68  thf('63', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.68  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['62', '63'])).
% 0.50/0.68  thf('65', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['55', '61', '64'])).
% 0.50/0.68  thf('66', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['55', '61', '64'])).
% 0.50/0.68  thf(t69_enumset1, axiom,
% 0.50/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.50/0.68  thf('67', plain,
% 0.50/0.68      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.50/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.68  thf(l51_zfmisc_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.68  thf('68', plain,
% 0.50/0.68      (![X68 : $i, X69 : $i]:
% 0.50/0.68         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.50/0.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.50/0.68  thf('69', plain,
% 0.50/0.68      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['67', '68'])).
% 0.50/0.68  thf('70', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.50/0.68  thf('71', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X26 @ X27)
% 0.50/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ 
% 0.50/0.68              (k5_xboole_0 @ X26 @ X27)))),
% 0.50/0.68      inference('demod', [status(thm)], ['1', '2'])).
% 0.50/0.68  thf('72', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X0 @ X0)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['70', '71'])).
% 0.50/0.68  thf('73', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.68  thf('74', plain,
% 0.50/0.68      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['72', '73'])).
% 0.50/0.68  thf('75', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.50/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.68  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['74', '75'])).
% 0.50/0.68  thf('77', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['69', '76'])).
% 0.50/0.68  thf('78', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.50/0.68      inference('sup+', [status(thm)], ['66', '77'])).
% 0.50/0.68  thf('79', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['65', '78'])).
% 0.50/0.68  thf('80', plain,
% 0.50/0.68      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.50/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.68  thf(t70_enumset1, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.50/0.68  thf('81', plain,
% 0.50/0.68      (![X41 : $i, X42 : $i]:
% 0.50/0.68         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.50/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.50/0.68  thf(d1_enumset1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.50/0.68       ( ![E:$i]:
% 0.50/0.68         ( ( r2_hidden @ E @ D ) <=>
% 0.50/0.68           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.50/0.68  thf(zf_stmt_2, axiom,
% 0.50/0.68    (![E:$i,C:$i,B:$i,A:$i]:
% 0.50/0.68     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.50/0.68       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_3, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.50/0.68       ( ![E:$i]:
% 0.50/0.68         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.50/0.68  thf('82', plain,
% 0.50/0.68      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.50/0.68         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36)
% 0.50/0.68          | (r2_hidden @ X33 @ X37)
% 0.50/0.68          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.68  thf('83', plain,
% 0.50/0.68      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.50/0.68         ((r2_hidden @ X33 @ (k1_enumset1 @ X36 @ X35 @ X34))
% 0.50/0.68          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 0.50/0.68      inference('simplify', [status(thm)], ['82'])).
% 0.50/0.68  thf('84', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.50/0.68          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.50/0.68      inference('sup+', [status(thm)], ['81', '83'])).
% 0.50/0.68  thf('85', plain,
% 0.50/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.50/0.68         (((X29) != (X28)) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X28))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.68  thf('86', plain,
% 0.50/0.68      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.50/0.68         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X28)),
% 0.50/0.68      inference('simplify', [status(thm)], ['85'])).
% 0.50/0.68  thf('87', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['84', '86'])).
% 0.50/0.68  thf('88', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['80', '87'])).
% 0.50/0.68  thf('89', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.50/0.68  thf('90', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf(t4_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.50/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.68  thf('91', plain,
% 0.50/0.68      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.50/0.68          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.50/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.68  thf('92', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.68          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('sup-', [status(thm)], ['90', '91'])).
% 0.50/0.68  thf('93', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['89', '92'])).
% 0.50/0.68  thf('94', plain,
% 0.50/0.68      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['88', '93'])).
% 0.50/0.68  thf('95', plain,
% 0.50/0.68      (~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ (k3_tarski @ k1_xboole_0)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['79', '94'])).
% 0.50/0.68  thf('96', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['65', '78'])).
% 0.50/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.68  thf('97', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.68  thf('98', plain,
% 0.50/0.68      (![X16 : $i, X17 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('99', plain,
% 0.50/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['97', '98'])).
% 0.50/0.68  thf(d7_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.50/0.68       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.68  thf('100', plain,
% 0.50/0.68      (![X4 : $i, X6 : $i]:
% 0.50/0.68         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.50/0.68  thf('101', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['99', '100'])).
% 0.50/0.68  thf('102', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.50/0.68      inference('simplify', [status(thm)], ['101'])).
% 0.50/0.68  thf('103', plain, ($false),
% 0.50/0.68      inference('demod', [status(thm)], ['95', '96', '102'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
