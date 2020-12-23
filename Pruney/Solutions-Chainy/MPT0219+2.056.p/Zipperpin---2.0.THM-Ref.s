%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ibq8Nsjv55

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:11 EST 2020

% Result     : Theorem 19.63s
% Output     : Refutation 19.68s
% Verified   : 
% Statistics : Number of formulae       :  326 (47261 expanded)
%              Number of leaves         :   45 (15801 expanded)
%              Depth                    :   42
%              Number of atoms          : 3028 (328194 expanded)
%              Number of equality atoms :  307 (42284 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('41',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['41','57'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('59',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( k3_enumset1 @ X85 @ X85 @ X86 @ X87 @ X88 )
      = ( k2_enumset1 @ X85 @ X86 @ X87 @ X88 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('60',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( k2_enumset1 @ X82 @ X82 @ X83 @ X84 )
      = ( k1_enumset1 @ X82 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('62',plain,(
    ! [X89: $i,X90: $i,X91: $i,X92: $i,X93: $i] :
      ( ( k4_enumset1 @ X89 @ X89 @ X90 @ X91 @ X92 @ X93 )
      = ( k3_enumset1 @ X89 @ X90 @ X91 @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t129_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('63',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k7_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X50 @ X51 @ X52 ) @ ( k4_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t129_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X7 @ X6 @ X5 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k7_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('71',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) @ ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('73',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k7_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_xboole_0 @ ( k1_tarski @ X41 ) @ ( k6_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k7_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('77',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X69 @ X68 ) @ ( k2_tarski @ X70 @ X68 ) )
      = ( k1_enumset1 @ X68 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X89: $i,X90: $i,X91: $i,X92: $i,X93: $i] :
      ( ( k4_enumset1 @ X89 @ X89 @ X90 @ X91 @ X92 @ X93 )
      = ( k3_enumset1 @ X89 @ X90 @ X91 @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('80',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( k3_enumset1 @ X85 @ X85 @ X86 @ X87 @ X88 )
      = ( k2_enumset1 @ X85 @ X86 @ X87 @ X88 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('83',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( k2_enumset1 @ X82 @ X82 @ X83 @ X84 )
      = ( k1_enumset1 @ X82 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( k2_enumset1 @ X82 @ X82 @ X83 @ X84 )
      = ( k1_enumset1 @ X82 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X80: $i,X81: $i] :
      ( ( k1_enumset1 @ X80 @ X80 @ X81 )
      = ( k2_tarski @ X80 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( k2_enumset1 @ X82 @ X82 @ X83 @ X84 )
      = ( k1_enumset1 @ X82 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('90',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) @ ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('93',plain,(
    ! [X100: $i,X101: $i,X102: $i,X103: $i,X104: $i,X105: $i,X106: $i] :
      ( ( k6_enumset1 @ X100 @ X100 @ X101 @ X102 @ X103 @ X104 @ X105 @ X106 )
      = ( k5_enumset1 @ X100 @ X101 @ X102 @ X103 @ X104 @ X105 @ X106 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('94',plain,(
    ! [X94: $i,X95: $i,X96: $i,X97: $i,X98: $i,X99: $i] :
      ( ( k5_enumset1 @ X94 @ X94 @ X95 @ X96 @ X97 @ X98 @ X99 )
      = ( k4_enumset1 @ X94 @ X95 @ X96 @ X97 @ X98 @ X99 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X4 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['85','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('98',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X69 @ X68 ) @ ( k2_tarski @ X70 @ X68 ) )
      = ( k1_enumset1 @ X68 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('101',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ( k2_enumset1 @ X82 @ X82 @ X83 @ X84 )
      = ( k1_enumset1 @ X82 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','78','99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('105',plain,(
    ! [X80: $i,X81: $i] :
      ( ( k1_enumset1 @ X80 @ X80 @ X81 )
      = ( k2_tarski @ X80 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('107',plain,(
    ! [X79: $i] :
      ( ( k2_tarski @ X79 @ X79 )
      = ( k1_tarski @ X79 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('108',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X69 @ X68 ) @ ( k2_tarski @ X70 @ X68 ) )
      = ( k1_enumset1 @ X68 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X80: $i,X81: $i] :
      ( ( k1_enumset1 @ X80 @ X80 @ X81 )
      = ( k2_tarski @ X80 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('116',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['122','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['113','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('143',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('144',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['142','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['153','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['152','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('168',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['166','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('184',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('186',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('188',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['183','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('195',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('201',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['41','57'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['205','210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['141','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','216'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('228',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('229',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('230',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['227','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['226','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('234',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('242',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('244',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['232','233','234','239','240','241','242','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['221','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','216'])).

thf('247',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['220','247'])).

thf('249',plain,(
    ! [X79: $i] :
      ( ( k2_tarski @ X79 @ X79 )
      = ( k1_tarski @ X79 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['249','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['248','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['112','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['248','260'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['58','265'])).

thf('267',plain,(
    ! [X80: $i,X81: $i] :
      ( ( k1_enumset1 @ X80 @ X80 @ X81 )
      = ( k2_tarski @ X80 @ X81 ) ) ),
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

thf('268',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('269',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['267','269'])).

thf('271',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('272',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['270','272'])).

thf('274',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['266','273'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('275',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('276',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['274','276'])).

thf('278',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['277','278'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ibq8Nsjv55
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.63/19.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.63/19.85  % Solved by: fo/fo7.sh
% 19.63/19.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.63/19.85  % done 11441 iterations in 19.394s
% 19.63/19.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.63/19.85  % SZS output start Refutation
% 19.63/19.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.63/19.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.63/19.85  thf(sk_B_type, type, sk_B: $i).
% 19.63/19.85  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 19.63/19.85                                           $i > $i > $i).
% 19.63/19.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 19.63/19.85  thf(sk_A_type, type, sk_A: $i).
% 19.63/19.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.63/19.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 19.63/19.85  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 19.63/19.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.63/19.85  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 19.63/19.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.63/19.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 19.63/19.85  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 19.63/19.85  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 19.63/19.85  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 19.63/19.85  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 19.63/19.85                                           $i > $i).
% 19.63/19.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.63/19.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 19.63/19.85  thf(t13_zfmisc_1, conjecture,
% 19.63/19.85    (![A:$i,B:$i]:
% 19.63/19.85     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 19.63/19.85         ( k1_tarski @ A ) ) =>
% 19.63/19.85       ( ( A ) = ( B ) ) ))).
% 19.63/19.85  thf(zf_stmt_0, negated_conjecture,
% 19.63/19.85    (~( ![A:$i,B:$i]:
% 19.63/19.85        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 19.63/19.85            ( k1_tarski @ A ) ) =>
% 19.63/19.85          ( ( A ) = ( B ) ) ) )),
% 19.63/19.85    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 19.63/19.85  thf('0', plain,
% 19.63/19.85      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 19.63/19.85         = (k1_tarski @ sk_A))),
% 19.63/19.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.63/19.85  thf(t98_xboole_1, axiom,
% 19.63/19.85    (![A:$i,B:$i]:
% 19.63/19.85     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 19.63/19.85  thf('1', plain,
% 19.63/19.85      (![X14 : $i, X15 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ X14 @ X15)
% 19.63/19.85           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.63/19.85  thf(idempotence_k3_xboole_0, axiom,
% 19.63/19.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 19.63/19.85  thf('2', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 19.63/19.85      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 19.63/19.85  thf(t100_xboole_1, axiom,
% 19.63/19.85    (![A:$i,B:$i]:
% 19.63/19.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 19.63/19.85  thf('3', plain,
% 19.63/19.85      (![X3 : $i, X4 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X3 @ X4)
% 19.63/19.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.63/19.85  thf('4', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.63/19.85  thf(t91_xboole_1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i]:
% 19.63/19.85     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 19.63/19.85       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 19.63/19.85  thf('5', plain,
% 19.63/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.63/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.63/19.85  thf('6', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 19.63/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['4', '5'])).
% 19.63/19.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.63/19.85  thf('7', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 19.63/19.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.63/19.85  thf(t28_xboole_1, axiom,
% 19.63/19.85    (![A:$i,B:$i]:
% 19.63/19.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 19.63/19.85  thf('8', plain,
% 19.63/19.85      (![X5 : $i, X6 : $i]:
% 19.63/19.85         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 19.63/19.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 19.63/19.85  thf('9', plain,
% 19.63/19.85      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('sup-', [status(thm)], ['7', '8'])).
% 19.63/19.85  thf(commutativity_k3_xboole_0, axiom,
% 19.63/19.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 19.63/19.85  thf('10', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.63/19.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.63/19.85  thf('11', plain,
% 19.63/19.85      (![X3 : $i, X4 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X3 @ X4)
% 19.63/19.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.63/19.85  thf('12', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X0 @ X1)
% 19.63/19.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['10', '11'])).
% 19.63/19.85  thf('13', plain,
% 19.63/19.85      (![X0 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['9', '12'])).
% 19.63/19.85  thf(t5_boole, axiom,
% 19.63/19.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 19.63/19.85  thf('14', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.63/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.63/19.85  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['13', '14'])).
% 19.63/19.85  thf(t48_xboole_1, axiom,
% 19.63/19.85    (![A:$i,B:$i]:
% 19.63/19.85     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.63/19.85  thf('16', plain,
% 19.63/19.85      (![X8 : $i, X9 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.63/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.63/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.63/19.85  thf('17', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['15', '16'])).
% 19.63/19.85  thf('18', plain,
% 19.63/19.85      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('sup-', [status(thm)], ['7', '8'])).
% 19.63/19.85  thf('19', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.63/19.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.63/19.85  thf('20', plain,
% 19.63/19.85      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['18', '19'])).
% 19.63/19.85  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('23', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['21', '22'])).
% 19.63/19.85  thf('24', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.63/19.85  thf('25', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 19.63/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['4', '5'])).
% 19.63/19.85  thf('26', plain,
% 19.63/19.85      (![X0 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 19.63/19.85           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['24', '25'])).
% 19.63/19.85  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('28', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.63/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.63/19.85  thf('29', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['27', '28'])).
% 19.63/19.85  thf('30', plain,
% 19.63/19.85      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 19.63/19.85      inference('demod', [status(thm)], ['26', '29'])).
% 19.63/19.85  thf('31', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['23', '30'])).
% 19.63/19.85  thf('32', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.63/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.63/19.85  thf('33', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X0 @ X1)
% 19.63/19.85           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['1', '32'])).
% 19.63/19.85  thf('34', plain,
% 19.63/19.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 19.63/19.85         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['0', '33'])).
% 19.63/19.85  thf('35', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.63/19.85  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('37', plain,
% 19.63/19.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['34', '35', '36'])).
% 19.63/19.85  thf('38', plain,
% 19.63/19.85      (![X8 : $i, X9 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.63/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.63/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.63/19.85  thf('39', plain,
% 19.63/19.85      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 19.63/19.85         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['37', '38'])).
% 19.63/19.85  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['13', '14'])).
% 19.63/19.85  thf('41', plain,
% 19.63/19.85      (((k1_tarski @ sk_B)
% 19.63/19.85         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 19.63/19.85      inference('demod', [status(thm)], ['39', '40'])).
% 19.63/19.85  thf('42', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.63/19.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.63/19.85  thf('43', plain,
% 19.63/19.85      (![X8 : $i, X9 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.63/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.63/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.63/19.85  thf('44', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.63/19.85  thf('45', plain,
% 19.63/19.85      (![X3 : $i, X4 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X3 @ X4)
% 19.63/19.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.63/19.85  thf('46', plain,
% 19.63/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.63/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.63/19.85  thf('47', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 19.63/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['45', '46'])).
% 19.63/19.85  thf('48', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 19.63/19.85           = (k5_xboole_0 @ X1 @ 
% 19.63/19.85              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 19.63/19.85      inference('sup+', [status(thm)], ['44', '47'])).
% 19.63/19.85  thf('49', plain,
% 19.63/19.85      (![X8 : $i, X9 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.63/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.63/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.63/19.85  thf('50', plain,
% 19.63/19.85      (![X14 : $i, X15 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ X14 @ X15)
% 19.63/19.85           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.63/19.85  thf('51', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 19.63/19.85           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['49', '50'])).
% 19.63/19.85  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('53', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 19.63/19.85           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['48', '51', '52'])).
% 19.63/19.85  thf('54', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.63/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.63/19.85  thf('55', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['53', '54'])).
% 19.63/19.85  thf('56', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['43', '55'])).
% 19.63/19.85  thf('57', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['42', '56'])).
% 19.63/19.85  thf('58', plain,
% 19.63/19.85      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 19.63/19.85         = (k1_tarski @ sk_A))),
% 19.63/19.85      inference('sup+', [status(thm)], ['41', '57'])).
% 19.63/19.85  thf(t72_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i]:
% 19.63/19.85     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 19.63/19.85  thf('59', plain,
% 19.63/19.85      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 19.63/19.85         ((k3_enumset1 @ X85 @ X85 @ X86 @ X87 @ X88)
% 19.63/19.85           = (k2_enumset1 @ X85 @ X86 @ X87 @ X88))),
% 19.63/19.85      inference('cnf', [status(esa)], [t72_enumset1])).
% 19.63/19.85  thf(t71_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i]:
% 19.63/19.85     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 19.63/19.85  thf('60', plain,
% 19.63/19.85      (![X82 : $i, X83 : $i, X84 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X82 @ X82 @ X83 @ X84)
% 19.63/19.85           = (k1_enumset1 @ X82 @ X83 @ X84))),
% 19.63/19.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 19.63/19.85  thf('61', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.63/19.85         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['59', '60'])).
% 19.63/19.85  thf(t73_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 19.63/19.85     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 19.63/19.85       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 19.63/19.85  thf('62', plain,
% 19.63/19.85      (![X89 : $i, X90 : $i, X91 : $i, X92 : $i, X93 : $i]:
% 19.63/19.85         ((k4_enumset1 @ X89 @ X89 @ X90 @ X91 @ X92 @ X93)
% 19.63/19.85           = (k3_enumset1 @ X89 @ X90 @ X91 @ X92 @ X93))),
% 19.63/19.85      inference('cnf', [status(esa)], [t73_enumset1])).
% 19.63/19.85  thf(t129_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 19.63/19.85     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 19.63/19.85       ( k2_xboole_0 @
% 19.63/19.85         ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ))).
% 19.63/19.85  thf('63', plain,
% 19.63/19.85      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, 
% 19.63/19.85         X57 : $i, X58 : $i]:
% 19.63/19.85         ((k7_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58)
% 19.63/19.85           = (k2_xboole_0 @ (k1_enumset1 @ X50 @ X51 @ X52) @ 
% 19.63/19.85              (k4_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t129_enumset1])).
% 19.63/19.85  thf('64', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 19.63/19.85         ((k7_enumset1 @ X7 @ X6 @ X5 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 19.63/19.85           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 19.63/19.85              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['62', '63'])).
% 19.63/19.85  thf('65', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 19.63/19.85         ((k7_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 19.63/19.85           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 19.63/19.85              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['61', '64'])).
% 19.63/19.85  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('67', plain,
% 19.63/19.85      (![X14 : $i, X15 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ X14 @ X15)
% 19.63/19.85           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.63/19.85  thf('68', plain,
% 19.63/19.85      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['66', '67'])).
% 19.63/19.85  thf('69', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.63/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.63/19.85  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 19.63/19.85      inference('demod', [status(thm)], ['68', '69'])).
% 19.63/19.85  thf(l75_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 19.63/19.85     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 19.63/19.85       ( k2_xboole_0 @
% 19.63/19.85         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 19.63/19.85  thf('71', plain,
% 19.63/19.85      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 19.63/19.85         X40 : $i]:
% 19.63/19.85         ((k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 19.63/19.85           = (k2_xboole_0 @ (k2_enumset1 @ X33 @ X34 @ X35 @ X36) @ 
% 19.63/19.85              (k2_enumset1 @ X37 @ X38 @ X39 @ X40)))),
% 19.63/19.85      inference('cnf', [status(esa)], [l75_enumset1])).
% 19.63/19.85  thf('72', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.63/19.85         ((k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0)
% 19.63/19.85           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['70', '71'])).
% 19.63/19.85  thf(t127_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 19.63/19.85     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 19.63/19.85       ( k2_xboole_0 @
% 19.63/19.85         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 19.63/19.85  thf('73', plain,
% 19.63/19.85      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 19.63/19.85         X48 : $i, X49 : $i]:
% 19.63/19.85         ((k7_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 19.63/19.85           = (k2_xboole_0 @ (k1_tarski @ X41) @ 
% 19.63/19.85              (k6_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t127_enumset1])).
% 19.63/19.85  thf('74', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 19.63/19.85         ((k7_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X3 @ X2 @ X1 @ X0)
% 19.63/19.85           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 19.63/19.85              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['72', '73'])).
% 19.63/19.85  thf('75', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ 
% 19.63/19.85           (k1_enumset1 @ X0 @ X0 @ X0))
% 19.63/19.85           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 19.63/19.85              (k2_enumset1 @ X0 @ X0 @ X0 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['65', '74'])).
% 19.63/19.85  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 19.63/19.85      inference('demod', [status(thm)], ['68', '69'])).
% 19.63/19.85  thf(t137_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i]:
% 19.63/19.85     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 19.63/19.85       ( k1_enumset1 @ A @ B @ C ) ))).
% 19.63/19.85  thf('77', plain,
% 19.63/19.85      (![X68 : $i, X69 : $i, X70 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k2_tarski @ X69 @ X68) @ (k2_tarski @ X70 @ X68))
% 19.63/19.85           = (k1_enumset1 @ X68 @ X69 @ X70))),
% 19.63/19.85      inference('cnf', [status(esa)], [t137_enumset1])).
% 19.63/19.85  thf('78', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['76', '77'])).
% 19.63/19.85  thf('79', plain,
% 19.63/19.85      (![X89 : $i, X90 : $i, X91 : $i, X92 : $i, X93 : $i]:
% 19.63/19.85         ((k4_enumset1 @ X89 @ X89 @ X90 @ X91 @ X92 @ X93)
% 19.63/19.85           = (k3_enumset1 @ X89 @ X90 @ X91 @ X92 @ X93))),
% 19.63/19.85      inference('cnf', [status(esa)], [t73_enumset1])).
% 19.63/19.85  thf('80', plain,
% 19.63/19.85      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 19.63/19.85         ((k3_enumset1 @ X85 @ X85 @ X86 @ X87 @ X88)
% 19.63/19.85           = (k2_enumset1 @ X85 @ X86 @ X87 @ X88))),
% 19.63/19.85      inference('cnf', [status(esa)], [t72_enumset1])).
% 19.63/19.85  thf('81', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.63/19.85         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 19.63/19.85           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['79', '80'])).
% 19.63/19.85  thf('82', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['76', '77'])).
% 19.63/19.85  thf('83', plain,
% 19.63/19.85      (![X82 : $i, X83 : $i, X84 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X82 @ X82 @ X83 @ X84)
% 19.63/19.85           = (k1_enumset1 @ X82 @ X83 @ X84))),
% 19.63/19.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 19.63/19.85  thf('84', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['82', '83'])).
% 19.63/19.85  thf('85', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['81', '84'])).
% 19.63/19.85  thf('86', plain,
% 19.63/19.85      (![X82 : $i, X83 : $i, X84 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X82 @ X82 @ X83 @ X84)
% 19.63/19.85           = (k1_enumset1 @ X82 @ X83 @ X84))),
% 19.63/19.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 19.63/19.85  thf(t70_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 19.63/19.85  thf('87', plain,
% 19.63/19.85      (![X80 : $i, X81 : $i]:
% 19.63/19.85         ((k1_enumset1 @ X80 @ X80 @ X81) = (k2_tarski @ X80 @ X81))),
% 19.63/19.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.63/19.85  thf('88', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['86', '87'])).
% 19.63/19.85  thf('89', plain,
% 19.63/19.85      (![X82 : $i, X83 : $i, X84 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X82 @ X82 @ X83 @ X84)
% 19.63/19.85           = (k1_enumset1 @ X82 @ X83 @ X84))),
% 19.63/19.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 19.63/19.85  thf('90', plain,
% 19.63/19.85      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 19.63/19.85         X40 : $i]:
% 19.63/19.85         ((k6_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 19.63/19.85           = (k2_xboole_0 @ (k2_enumset1 @ X33 @ X34 @ X35 @ X36) @ 
% 19.63/19.85              (k2_enumset1 @ X37 @ X38 @ X39 @ X40)))),
% 19.63/19.85      inference('cnf', [status(esa)], [l75_enumset1])).
% 19.63/19.85  thf('91', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 19.63/19.85         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 19.63/19.85           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 19.63/19.85              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['89', '90'])).
% 19.63/19.85  thf('92', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 19.63/19.85         ((k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X4 @ X3 @ X2)
% 19.63/19.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 19.63/19.85              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['88', '91'])).
% 19.63/19.85  thf(t75_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 19.63/19.85     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 19.63/19.85       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 19.63/19.85  thf('93', plain,
% 19.63/19.85      (![X100 : $i, X101 : $i, X102 : $i, X103 : $i, X104 : $i, X105 : $i, 
% 19.63/19.85         X106 : $i]:
% 19.63/19.85         ((k6_enumset1 @ X100 @ X100 @ X101 @ X102 @ X103 @ X104 @ X105 @ X106)
% 19.63/19.85           = (k5_enumset1 @ X100 @ X101 @ X102 @ X103 @ X104 @ X105 @ X106))),
% 19.63/19.85      inference('cnf', [status(esa)], [t75_enumset1])).
% 19.63/19.85  thf(t74_enumset1, axiom,
% 19.63/19.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.63/19.85     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 19.63/19.85       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 19.63/19.85  thf('94', plain,
% 19.63/19.85      (![X94 : $i, X95 : $i, X96 : $i, X97 : $i, X98 : $i, X99 : $i]:
% 19.63/19.85         ((k5_enumset1 @ X94 @ X94 @ X95 @ X96 @ X97 @ X98 @ X99)
% 19.63/19.85           = (k4_enumset1 @ X94 @ X95 @ X96 @ X97 @ X98 @ X99))),
% 19.63/19.85      inference('cnf', [status(esa)], [t74_enumset1])).
% 19.63/19.85  thf('95', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 19.63/19.85         ((k4_enumset1 @ X1 @ X0 @ X4 @ X4 @ X3 @ X2)
% 19.63/19.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 19.63/19.85              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 19.63/19.85      inference('demod', [status(thm)], ['92', '93', '94'])).
% 19.63/19.85  thf('96', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0)
% 19.63/19.85           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 19.63/19.85              (k1_enumset1 @ X0 @ X1 @ X1)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['85', '95'])).
% 19.63/19.85  thf('97', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['76', '77'])).
% 19.63/19.85  thf('98', plain,
% 19.63/19.85      (![X68 : $i, X69 : $i, X70 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k2_tarski @ X69 @ X68) @ (k2_tarski @ X70 @ X68))
% 19.63/19.85           = (k1_enumset1 @ X68 @ X69 @ X70))),
% 19.63/19.85      inference('cnf', [status(esa)], [t137_enumset1])).
% 19.63/19.85  thf('99', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['96', '97', '98'])).
% 19.63/19.85  thf('100', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['96', '97', '98'])).
% 19.63/19.85  thf('101', plain,
% 19.63/19.85      (![X82 : $i, X83 : $i, X84 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X82 @ X82 @ X83 @ X84)
% 19.63/19.85           = (k1_enumset1 @ X82 @ X83 @ X84))),
% 19.63/19.85      inference('cnf', [status(esa)], [t71_enumset1])).
% 19.63/19.85  thf('102', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['100', '101'])).
% 19.63/19.85  thf('103', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X0 @ X0))
% 19.63/19.85           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 19.63/19.85      inference('demod', [status(thm)], ['75', '78', '99', '102'])).
% 19.63/19.85  thf('104', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['96', '97', '98'])).
% 19.63/19.85  thf('105', plain,
% 19.63/19.85      (![X80 : $i, X81 : $i]:
% 19.63/19.85         ((k1_enumset1 @ X80 @ X80 @ X81) = (k2_tarski @ X80 @ X81))),
% 19.63/19.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.63/19.85  thf('106', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['104', '105'])).
% 19.63/19.85  thf(t69_enumset1, axiom,
% 19.63/19.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 19.63/19.85  thf('107', plain,
% 19.63/19.85      (![X79 : $i]: ((k2_tarski @ X79 @ X79) = (k1_tarski @ X79))),
% 19.63/19.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 19.63/19.85  thf('108', plain,
% 19.63/19.85      (![X68 : $i, X69 : $i, X70 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k2_tarski @ X69 @ X68) @ (k2_tarski @ X70 @ X68))
% 19.63/19.85           = (k1_enumset1 @ X68 @ X69 @ X70))),
% 19.63/19.85      inference('cnf', [status(esa)], [t137_enumset1])).
% 19.63/19.85  thf('109', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 19.63/19.85           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['107', '108'])).
% 19.63/19.85  thf('110', plain,
% 19.63/19.85      (![X80 : $i, X81 : $i]:
% 19.63/19.85         ((k1_enumset1 @ X80 @ X80 @ X81) = (k2_tarski @ X80 @ X81))),
% 19.63/19.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.63/19.85  thf('111', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 19.63/19.85           = (k2_tarski @ X0 @ X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['109', '110'])).
% 19.63/19.85  thf('112', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 19.63/19.85           = (k2_tarski @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['106', '111'])).
% 19.63/19.85  thf('113', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 19.63/19.85           = (k2_tarski @ X0 @ X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['109', '110'])).
% 19.63/19.85  thf('114', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.63/19.85  thf('115', plain,
% 19.63/19.85      (![X14 : $i, X15 : $i]:
% 19.63/19.85         ((k2_xboole_0 @ X14 @ X15)
% 19.63/19.85           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.63/19.85  thf('116', plain,
% 19.63/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.63/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.63/19.85  thf('117', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 19.63/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['115', '116'])).
% 19.63/19.85  thf('118', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 19.63/19.85           = (k5_xboole_0 @ X0 @ 
% 19.63/19.85              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 19.63/19.85      inference('sup+', [status(thm)], ['114', '117'])).
% 19.63/19.85  thf('119', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('120', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 19.63/19.85           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['118', '119'])).
% 19.63/19.85  thf('121', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.63/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.63/19.85  thf('122', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 19.63/19.85           = (X0))),
% 19.63/19.85      inference('demod', [status(thm)], ['120', '121'])).
% 19.63/19.85  thf('123', plain,
% 19.63/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.63/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.63/19.85  thf('124', plain,
% 19.63/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.63/19.85  thf('125', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 19.63/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 19.63/19.85      inference('sup+', [status(thm)], ['123', '124'])).
% 19.63/19.85  thf('126', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.63/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.63/19.85  thf('127', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k1_xboole_0)
% 19.63/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 19.63/19.85      inference('demod', [status(thm)], ['125', '126'])).
% 19.63/19.85  thf('128', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.63/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.63/19.85  thf('129', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 19.63/19.85           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['127', '128'])).
% 19.63/19.85  thf('130', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.63/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.63/19.85  thf('131', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['129', '130'])).
% 19.63/19.85  thf('132', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.63/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.63/19.85  thf('133', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.63/19.85  thf('134', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 19.63/19.85           = (X0))),
% 19.63/19.85      inference('demod', [status(thm)], ['122', '133'])).
% 19.63/19.85  thf('135', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ 
% 19.63/19.85           (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X1)) @ 
% 19.63/19.85           (k2_tarski @ X1 @ X0)) = (k1_tarski @ X1))),
% 19.63/19.85      inference('sup+', [status(thm)], ['113', '134'])).
% 19.63/19.85  thf('136', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.63/19.85  thf('137', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 19.63/19.85           (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X1)))
% 19.63/19.85           = (k1_tarski @ X1))),
% 19.63/19.85      inference('demod', [status(thm)], ['135', '136'])).
% 19.63/19.85  thf('138', plain,
% 19.63/19.85      (![X3 : $i, X4 : $i]:
% 19.63/19.85         ((k4_xboole_0 @ X3 @ X4)
% 19.63/19.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 19.63/19.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.63/19.85  thf('139', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.63/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.63/19.85  thf('140', plain,
% 19.63/19.85      (![X0 : $i, X1 : $i]:
% 19.63/19.85         ((k3_xboole_0 @ X1 @ X0)
% 19.63/19.85           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.63/19.85      inference('sup+', [status(thm)], ['138', '139'])).
% 19.63/19.85  thf('141', plain,
% 19.63/19.85      (![X0 : $i]:
% 19.63/19.85         ((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 19.63/19.85           = (k1_tarski @ X0))),
% 19.63/19.85      inference('sup+', [status(thm)], ['137', '140'])).
% 19.68/19.85  thf('142', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.68/19.85  thf('143', plain,
% 19.68/19.85      (![X8 : $i, X9 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.68/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.68/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.68/19.85  thf('144', plain,
% 19.68/19.85      (![X8 : $i, X9 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.68/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.68/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.68/19.85  thf('145', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['143', '144'])).
% 19.68/19.85  thf('146', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['138', '139'])).
% 19.68/19.85  thf('147', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['145', '146'])).
% 19.68/19.85  thf('148', plain,
% 19.68/19.85      (![X3 : $i, X4 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X3 @ X4)
% 19.68/19.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.68/19.85  thf('149', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['147', '148'])).
% 19.68/19.85  thf('150', plain,
% 19.68/19.85      (![X8 : $i, X9 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.68/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.68/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.68/19.85  thf('151', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k3_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['149', '150'])).
% 19.68/19.85  thf('152', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k3_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('sup+', [status(thm)], ['142', '151'])).
% 19.68/19.85  thf('153', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 19.68/19.85  thf('154', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k3_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['149', '150'])).
% 19.68/19.85  thf('155', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X0 @ X1)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['10', '11'])).
% 19.68/19.85  thf('156', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 19.68/19.85           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['154', '155'])).
% 19.68/19.85  thf('157', plain,
% 19.68/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.68/19.85  thf('158', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.68/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.68/19.85  thf('159', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 19.68/19.85      inference('demod', [status(thm)], ['156', '157', '158'])).
% 19.68/19.85  thf('160', plain,
% 19.68/19.85      (![X14 : $i, X15 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X14 @ X15)
% 19.68/19.85           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.68/19.85  thf('161', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 19.68/19.85           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['159', '160'])).
% 19.68/19.85  thf('162', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.68/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.68/19.85  thf('163', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['161', '162'])).
% 19.68/19.85  thf('164', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['153', '163'])).
% 19.68/19.85  thf('165', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k3_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('sup+', [status(thm)], ['152', '164'])).
% 19.68/19.85  thf('166', plain,
% 19.68/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.68/19.85  thf('167', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X0 @ X1)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['10', '11'])).
% 19.68/19.85  thf('168', plain,
% 19.68/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.68/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.68/19.85  thf('169', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['167', '168'])).
% 19.68/19.85  thf('170', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X0 @ 
% 19.68/19.85              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['166', '169'])).
% 19.68/19.85  thf('171', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.68/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.68/19.85  thf('172', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 19.68/19.85      inference('demod', [status(thm)], ['170', '171'])).
% 19.68/19.85  thf('173', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 19.68/19.85      inference('cnf', [status(esa)], [t5_boole])).
% 19.68/19.85  thf('174', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['172', '173'])).
% 19.68/19.85  thf('175', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['115', '116'])).
% 19.68/19.85  thf('176', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['174', '175'])).
% 19.68/19.85  thf('177', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.68/19.85  thf('178', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['176', '177'])).
% 19.68/19.85  thf('179', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['45', '46'])).
% 19.68/19.85  thf('180', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['178', '179'])).
% 19.68/19.85  thf('181', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.68/19.85  thf('182', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['180', '181'])).
% 19.68/19.85  thf('183', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 19.68/19.85      inference('demod', [status(thm)], ['129', '130'])).
% 19.68/19.85  thf('184', plain,
% 19.68/19.85      (((k1_tarski @ sk_B)
% 19.68/19.85         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 19.68/19.85      inference('demod', [status(thm)], ['39', '40'])).
% 19.68/19.85  thf('185', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X0 @ X1)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['10', '11'])).
% 19.68/19.85  thf('186', plain,
% 19.68/19.85      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 19.68/19.85         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['184', '185'])).
% 19.68/19.85  thf('187', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.68/19.85  thf('188', plain,
% 19.68/19.85      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 19.68/19.85         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 19.68/19.85      inference('demod', [status(thm)], ['186', '187'])).
% 19.68/19.85  thf('189', plain,
% 19.68/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.68/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.68/19.85  thf('190', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ 
% 19.68/19.85           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 19.68/19.85           = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 19.68/19.85              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['188', '189'])).
% 19.68/19.85  thf('191', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ 
% 19.68/19.85           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 19.68/19.85           (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 19.68/19.85           = (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['183', '190'])).
% 19.68/19.85  thf('192', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.68/19.85  thf('193', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 19.68/19.85           = (k5_xboole_0 @ 
% 19.68/19.85              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 19.68/19.85              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['191', '192'])).
% 19.68/19.85  thf('194', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.68/19.85  thf('195', plain,
% 19.68/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.68/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.68/19.85  thf('196', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['194', '195'])).
% 19.68/19.85  thf('197', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ X1)
% 19.68/19.85           = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0) @ 
% 19.68/19.85              (k5_xboole_0 @ 
% 19.68/19.85               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X1)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['193', '196'])).
% 19.68/19.85  thf('198', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['194', '195'])).
% 19.68/19.85  thf('199', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['194', '195'])).
% 19.68/19.85  thf('200', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['115', '116'])).
% 19.68/19.85  thf('201', plain,
% 19.68/19.85      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 19.68/19.85         = (k1_tarski @ sk_A))),
% 19.68/19.85      inference('sup+', [status(thm)], ['41', '57'])).
% 19.68/19.85  thf('202', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ X1))
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['197', '198', '199', '200', '201'])).
% 19.68/19.85  thf('203', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.68/19.85  thf('204', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ 
% 19.68/19.85              (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X1 @ X0))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['202', '203'])).
% 19.68/19.85  thf('205', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 19.68/19.85              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['182', '204'])).
% 19.68/19.85  thf('206', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.68/19.85  thf('207', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ X1))
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['197', '198', '199', '200', '201'])).
% 19.68/19.85  thf('208', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k1_tarski @ sk_A))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['206', '207'])).
% 19.68/19.85  thf('209', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['194', '195'])).
% 19.68/19.85  thf('210', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ sk_A)))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['208', '209'])).
% 19.68/19.85  thf('211', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['115', '116'])).
% 19.68/19.85  thf('212', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k1_tarski @ sk_A)))),
% 19.68/19.85      inference('demod', [status(thm)], ['205', '210', '211'])).
% 19.68/19.85  thf('213', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 19.68/19.85      inference('demod', [status(thm)], ['129', '130'])).
% 19.68/19.85  thf('214', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 19.68/19.85           (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X1 @ X0)))
% 19.68/19.85           = (k2_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('sup+', [status(thm)], ['212', '213'])).
% 19.68/19.85  thf('215', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.68/19.85  thf('216', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('demod', [status(thm)], ['214', '215'])).
% 19.68/19.85  thf('217', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['165', '216'])).
% 19.68/19.85  thf('218', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 19.68/19.85           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 19.68/19.85              (k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['141', '217'])).
% 19.68/19.85  thf('219', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['161', '162'])).
% 19.68/19.85  thf('220', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 19.68/19.85           = (k1_tarski @ X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['218', '219'])).
% 19.68/19.85  thf('221', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['165', '216'])).
% 19.68/19.85  thf('222', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('demod', [status(thm)], ['214', '215'])).
% 19.68/19.85  thf('223', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['176', '177'])).
% 19.68/19.85  thf('224', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (k5_xboole_0 @ X0 @ X1))),
% 19.68/19.85      inference('sup+', [status(thm)], ['222', '223'])).
% 19.68/19.85  thf('225', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.68/19.85  thf('226', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X0 @ X1)
% 19.68/19.85           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['224', '225'])).
% 19.68/19.85  thf('227', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.68/19.85  thf('228', plain,
% 19.68/19.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 19.68/19.85           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 19.68/19.85  thf('229', plain,
% 19.68/19.85      (![X14 : $i, X15 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X14 @ X15)
% 19.68/19.85           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.68/19.85  thf('230', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ 
% 19.68/19.85              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['228', '229'])).
% 19.68/19.85  thf('231', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ 
% 19.68/19.85              (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['227', '230'])).
% 19.68/19.85  thf('232', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ 
% 19.68/19.85           (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 19.68/19.85           X2)
% 19.68/19.85           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ 
% 19.68/19.85              (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 19.68/19.85               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['226', '231'])).
% 19.68/19.85  thf('233', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['194', '195'])).
% 19.68/19.85  thf('234', plain,
% 19.68/19.85      (![X3 : $i, X4 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X3 @ X4)
% 19.68/19.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 19.68/19.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.68/19.85  thf('235', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 19.68/19.85           = (X0))),
% 19.68/19.85      inference('demod', [status(thm)], ['180', '181'])).
% 19.68/19.85  thf('236', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['6', '31'])).
% 19.68/19.85  thf('237', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['235', '236'])).
% 19.68/19.85  thf('238', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['131', '132'])).
% 19.68/19.85  thf('239', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['237', '238'])).
% 19.68/19.85  thf('240', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['194', '195'])).
% 19.68/19.85  thf('241', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['45', '46'])).
% 19.68/19.85  thf('242', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['115', '116'])).
% 19.68/19.85  thf('243', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['237', '238'])).
% 19.68/19.85  thf('244', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 19.68/19.85           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)],
% 19.68/19.85                ['232', '233', '234', '239', '240', '241', '242', '243'])).
% 19.68/19.85  thf('245', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k2_xboole_0 @ X2 @ 
% 19.68/19.85              (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['221', '244'])).
% 19.68/19.85  thf('246', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k3_xboole_0 @ X1 @ X0)
% 19.68/19.85           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['165', '216'])).
% 19.68/19.85  thf('247', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 19.68/19.85           = (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 19.68/19.85      inference('demod', [status(thm)], ['245', '246'])).
% 19.68/19.85  thf('248', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ X1)
% 19.68/19.85           = (k2_xboole_0 @ X1 @ 
% 19.68/19.85              (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))))),
% 19.68/19.85      inference('sup+', [status(thm)], ['220', '247'])).
% 19.68/19.85  thf('249', plain,
% 19.68/19.85      (![X79 : $i]: ((k2_tarski @ X79 @ X79) = (k1_tarski @ X79))),
% 19.68/19.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 19.68/19.85  thf('250', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 19.68/19.85           = (k2_tarski @ X0 @ X1))),
% 19.68/19.85      inference('demod', [status(thm)], ['109', '110'])).
% 19.68/19.85  thf('251', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X0 @ X1)
% 19.68/19.85           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['1', '32'])).
% 19.68/19.85  thf('252', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X1))
% 19.68/19.85           = (k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['250', '251'])).
% 19.68/19.85  thf('253', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 19.68/19.85           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['249', '252'])).
% 19.68/19.85  thf('254', plain,
% 19.68/19.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['2', '3'])).
% 19.68/19.85  thf('255', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 19.68/19.85      inference('demod', [status(thm)], ['17', '20'])).
% 19.68/19.85  thf('256', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 19.68/19.85           = (k1_xboole_0))),
% 19.68/19.85      inference('demod', [status(thm)], ['253', '254', '255'])).
% 19.68/19.85  thf('257', plain,
% 19.68/19.85      (![X8 : $i, X9 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 19.68/19.85           = (k3_xboole_0 @ X8 @ X9))),
% 19.68/19.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 19.68/19.85  thf('258', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0)
% 19.68/19.85           = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['256', '257'])).
% 19.68/19.85  thf('259', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['13', '14'])).
% 19.68/19.85  thf('260', plain,
% 19.68/19.85      (![X0 : $i]:
% 19.68/19.85         ((k2_tarski @ X0 @ X0)
% 19.68/19.85           = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['258', '259'])).
% 19.68/19.85  thf('261', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ X1)
% 19.68/19.85           = (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['248', '260'])).
% 19.68/19.85  thf('262', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_tarski @ X1 @ X0)
% 19.68/19.85           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X1)))),
% 19.68/19.85      inference('sup+', [status(thm)], ['112', '261'])).
% 19.68/19.85  thf('263', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_tarski @ X0 @ X1)
% 19.68/19.85           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['103', '262'])).
% 19.68/19.85  thf('264', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k1_tarski @ X0) @ X1)
% 19.68/19.85           = (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 19.68/19.85      inference('demod', [status(thm)], ['248', '260'])).
% 19.68/19.85  thf('265', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]:
% 19.68/19.85         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 19.68/19.85           = (k2_tarski @ X1 @ X0))),
% 19.68/19.85      inference('sup+', [status(thm)], ['263', '264'])).
% 19.68/19.85  thf('266', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 19.68/19.85      inference('demod', [status(thm)], ['58', '265'])).
% 19.68/19.85  thf('267', plain,
% 19.68/19.85      (![X80 : $i, X81 : $i]:
% 19.68/19.85         ((k1_enumset1 @ X80 @ X80 @ X81) = (k2_tarski @ X80 @ X81))),
% 19.68/19.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.68/19.85  thf(d1_enumset1, axiom,
% 19.68/19.85    (![A:$i,B:$i,C:$i,D:$i]:
% 19.68/19.85     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 19.68/19.85       ( ![E:$i]:
% 19.68/19.85         ( ( r2_hidden @ E @ D ) <=>
% 19.68/19.85           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 19.68/19.85  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 19.68/19.85  thf(zf_stmt_2, axiom,
% 19.68/19.85    (![E:$i,C:$i,B:$i,A:$i]:
% 19.68/19.85     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 19.68/19.85       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 19.68/19.85  thf(zf_stmt_3, axiom,
% 19.68/19.85    (![A:$i,B:$i,C:$i,D:$i]:
% 19.68/19.85     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 19.68/19.85       ( ![E:$i]:
% 19.68/19.85         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 19.68/19.85  thf('268', plain,
% 19.68/19.85      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 19.68/19.85         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 19.68/19.85          | (r2_hidden @ X21 @ X25)
% 19.68/19.85          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 19.68/19.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 19.68/19.85  thf('269', plain,
% 19.68/19.85      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 19.68/19.85         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 19.68/19.85          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 19.68/19.85      inference('simplify', [status(thm)], ['268'])).
% 19.68/19.85  thf('270', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.68/19.85         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 19.68/19.85          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 19.68/19.85      inference('sup+', [status(thm)], ['267', '269'])).
% 19.68/19.85  thf('271', plain,
% 19.68/19.85      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 19.68/19.85         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 19.68/19.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 19.68/19.85  thf('272', plain,
% 19.68/19.85      (![X16 : $i, X18 : $i, X19 : $i]:
% 19.68/19.85         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 19.68/19.85      inference('simplify', [status(thm)], ['271'])).
% 19.68/19.85  thf('273', plain,
% 19.68/19.85      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 19.68/19.85      inference('sup-', [status(thm)], ['270', '272'])).
% 19.68/19.85  thf('274', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 19.68/19.85      inference('sup+', [status(thm)], ['266', '273'])).
% 19.68/19.85  thf(d1_tarski, axiom,
% 19.68/19.85    (![A:$i,B:$i]:
% 19.68/19.85     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 19.68/19.85       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 19.68/19.85  thf('275', plain,
% 19.68/19.85      (![X28 : $i, X30 : $i, X31 : $i]:
% 19.68/19.85         (~ (r2_hidden @ X31 @ X30)
% 19.68/19.85          | ((X31) = (X28))
% 19.68/19.85          | ((X30) != (k1_tarski @ X28)))),
% 19.68/19.85      inference('cnf', [status(esa)], [d1_tarski])).
% 19.68/19.85  thf('276', plain,
% 19.68/19.85      (![X28 : $i, X31 : $i]:
% 19.68/19.85         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 19.68/19.85      inference('simplify', [status(thm)], ['275'])).
% 19.68/19.85  thf('277', plain, (((sk_B) = (sk_A))),
% 19.68/19.85      inference('sup-', [status(thm)], ['274', '276'])).
% 19.68/19.85  thf('278', plain, (((sk_A) != (sk_B))),
% 19.68/19.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.68/19.85  thf('279', plain, ($false),
% 19.68/19.85      inference('simplify_reflect-', [status(thm)], ['277', '278'])).
% 19.68/19.85  
% 19.68/19.85  % SZS output end Refutation
% 19.68/19.85  
% 19.68/19.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
