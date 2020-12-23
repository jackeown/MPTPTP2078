%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aihtAGws9Z

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:22 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  158 (1319 expanded)
%              Number of leaves         :   24 ( 431 expanded)
%              Depth                    :   33
%              Number of atoms          : 1381 (11486 expanded)
%              Number of equality atoms :  147 (1293 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_xboole_0 @ X43 @ ( k1_tarski @ X42 ) )
        = ( k1_tarski @ X42 ) )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['20','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','19','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('54',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('74',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('103',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['89','101','102'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('104',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k4_xboole_0 @ X51 @ ( k1_tarski @ X52 ) )
        = X51 )
      | ( r2_hidden @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('111',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('113',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('116',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('118',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','60'])).

thf('119',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('122',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['103','120','121'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('123',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('124',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('125',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('126',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X46: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X46 ) ) ),
    inference(demod,[status(thm)],['124','129'])).

thf('131',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,(
    $false ),
    inference(simplify,[status(thm)],['131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aihtAGws9Z
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:40:14 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 499 iterations in 0.242s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(t68_zfmisc_1, conjecture,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.71       ( r2_hidden @ A @ B ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i]:
% 0.52/0.71        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.71          ( r2_hidden @ A @ B ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      (((r2_hidden @ sk_A @ sk_B)
% 0.52/0.71        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.52/0.71         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.52/0.71        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.52/0.71       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.52/0.71      inference('split', [status(esa)], ['2'])).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf(l31_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r2_hidden @ A @ B ) =>
% 0.52/0.71       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X42 : $i, X43 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X43 @ (k1_tarski @ X42)) = (k1_tarski @ X42))
% 0.52/0.71          | ~ (r2_hidden @ X42 @ X43))),
% 0.52/0.71      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.71  thf(t100_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.52/0.71          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf(t95_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k3_xboole_0 @ A @ B ) =
% 0.52/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X10 @ X11)
% 0.52/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.52/0.71              (k2_xboole_0 @ X10 @ X11)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X10 @ X11)
% 0.52/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.52/0.71              (k5_xboole_0 @ X10 @ X11)))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['9', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.71          = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.71             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['8', '13'])).
% 0.52/0.71  thf(commutativity_k2_tarski, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X12 : $i, X13 : $i]:
% 0.52/0.71         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.52/0.71  thf(l51_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (![X44 : $i, X45 : $i]:
% 0.52/0.71         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.52/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['15', '16'])).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X44 : $i, X45 : $i]:
% 0.52/0.71         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.52/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf(t92_xboole_1, axiom,
% 0.52/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.71  thf('20', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.52/0.71          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X10 @ X11)
% 0.52/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.52/0.71              (k5_xboole_0 @ X10 @ X11)))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.52/0.71          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      ((((k1_tarski @ sk_A)
% 0.52/0.71          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('27', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.52/0.71          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.71  thf(t91_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.52/0.71            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71          (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['27', '30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf(t5_boole, axiom,
% 0.52/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.71  thf('35', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.71  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['31', '32', '33', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          ((k5_xboole_0 @ sk_B @ X0)
% 0.52/0.71            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['37', '38'])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          ((k5_xboole_0 @ sk_B @ X0)
% 0.52/0.71            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71               (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['26', '39'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['25', '40'])).
% 0.52/0.71  thf('42', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71          = (k1_xboole_0)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.71            = (k5_xboole_0 @ sk_B @ 
% 0.52/0.71               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['43', '44'])).
% 0.52/0.71  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          ((X0)
% 0.52/0.71            = (k5_xboole_0 @ sk_B @ 
% 0.52/0.71               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.52/0.71          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['20', '47'])).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.52/0.71  thf('52', plain,
% 0.52/0.71      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.71          = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['14', '19', '51'])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          ((k5_xboole_0 @ sk_B @ X0)
% 0.52/0.71            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71               (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['26', '39'])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B @ sk_B)
% 0.52/0.71          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['52', '53'])).
% 0.52/0.71  thf('55', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('56', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.52/0.71         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['2'])).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.52/0.71             ((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.52/0.71       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.71      inference('simplify', [status(thm)], ['59'])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.52/0.71       ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['3', '60', '61'])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('65', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['65', '66'])).
% 0.52/0.71  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X1 @ X0)
% 0.52/0.71           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['64', '69'])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.71         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['63', '70'])).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X10 @ X11)
% 0.52/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.52/0.71              (k5_xboole_0 @ X10 @ X11)))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      (![X10 : $i, X11 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X10 @ X11)
% 0.52/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.52/0.71              (k5_xboole_0 @ X10 @ X11)))),
% 0.52/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.52/0.71           = (k5_xboole_0 @ 
% 0.52/0.71              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.52/0.71              (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['75', '76'])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.52/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.52/0.71              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.71  thf('80', plain,
% 0.52/0.71      (((k3_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.71         (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.52/0.71         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71            (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.71             (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['74', '79'])).
% 0.52/0.71  thf('81', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('82', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('83', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('85', plain,
% 0.52/0.71      (((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.52/0.71            (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.71      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.52/0.71  thf('86', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('87', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.71  thf('88', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['86', '87'])).
% 0.52/0.71  thf('89', plain,
% 0.52/0.71      (((k1_tarski @ sk_A)
% 0.52/0.71         = (k5_xboole_0 @ 
% 0.52/0.71            (k2_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.52/0.71            (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['85', '88'])).
% 0.52/0.71  thf('90', plain,
% 0.52/0.71      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 0.52/0.71  thf('91', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['9', '12'])).
% 0.52/0.71  thf('92', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['86', '87'])).
% 0.52/0.71  thf('93', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k2_xboole_0 @ X1 @ X0)
% 0.52/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['91', '92'])).
% 0.52/0.71  thf('94', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.71  thf('95', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('96', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k2_xboole_0 @ X1 @ X0)
% 0.52/0.71           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.52/0.71  thf('97', plain,
% 0.52/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.71         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['90', '96'])).
% 0.52/0.71  thf('98', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('99', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('101', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.52/0.71  thf('102', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.52/0.71  thf('103', plain,
% 0.52/0.71      (((k1_tarski @ sk_A)
% 0.52/0.71         = (k5_xboole_0 @ 
% 0.52/0.71            (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.52/0.71            (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.71      inference('demod', [status(thm)], ['89', '101', '102'])).
% 0.52/0.71  thf(t65_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.52/0.71       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.52/0.71  thf('104', plain,
% 0.52/0.71      (![X51 : $i, X52 : $i]:
% 0.52/0.71         (((k4_xboole_0 @ X51 @ (k1_tarski @ X52)) = (X51))
% 0.52/0.71          | (r2_hidden @ X52 @ X51))),
% 0.52/0.71      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.52/0.71  thf('105', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X1 @ X0)
% 0.52/0.71           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['64', '69'])).
% 0.52/0.71  thf('106', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k5_xboole_0 @ X0 @ X0))
% 0.52/0.71          | (r2_hidden @ X1 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['104', '105'])).
% 0.52/0.71  thf('107', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('108', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0))
% 0.52/0.71          | (r2_hidden @ X1 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['106', '107'])).
% 0.52/0.71  thf('109', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.52/0.71  thf('110', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.52/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.52/0.71              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.71  thf('111', plain,
% 0.52/0.71      (((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71            (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['109', '110'])).
% 0.52/0.71  thf('112', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.52/0.71  thf('113', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.71            (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.71      inference('demod', [status(thm)], ['111', '112'])).
% 0.52/0.71  thf('114', plain,
% 0.52/0.71      ((((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71          = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.52/0.71             (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.52/0.71        | (r2_hidden @ sk_A @ sk_B))),
% 0.52/0.71      inference('sup+', [status(thm)], ['108', '113'])).
% 0.52/0.71  thf('115', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.52/0.71  thf('116', plain,
% 0.52/0.71      ((((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71          = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.52/0.71        | (r2_hidden @ sk_A @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['114', '115'])).
% 0.52/0.71  thf('117', plain,
% 0.52/0.71      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.71      inference('split', [status(esa)], ['2'])).
% 0.52/0.71  thf('118', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['3', '60'])).
% 0.52/0.71  thf('119', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 0.52/0.71  thf('120', plain,
% 0.52/0.71      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.71         = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('clc', [status(thm)], ['116', '119'])).
% 0.52/0.71  thf('121', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('122', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['103', '120', '121'])).
% 0.52/0.71  thf(t20_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.52/0.71         ( k1_tarski @ A ) ) <=>
% 0.52/0.71       ( ( A ) != ( B ) ) ))).
% 0.52/0.71  thf('123', plain,
% 0.52/0.71      (![X46 : $i, X47 : $i]:
% 0.52/0.71         (((X47) != (X46))
% 0.52/0.71          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 0.52/0.71              != (k1_tarski @ X47)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.52/0.71  thf('124', plain,
% 0.52/0.71      (![X46 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 0.52/0.71           != (k1_tarski @ X46))),
% 0.52/0.71      inference('simplify', [status(thm)], ['123'])).
% 0.52/0.71  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.71  thf('125', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.71  thf('126', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.71           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('127', plain,
% 0.52/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['125', '126'])).
% 0.52/0.71  thf('128', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('129', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['127', '128'])).
% 0.52/0.71  thf('130', plain, (![X46 : $i]: ((k1_xboole_0) != (k1_tarski @ X46))),
% 0.52/0.71      inference('demod', [status(thm)], ['124', '129'])).
% 0.52/0.71  thf('131', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['122', '130'])).
% 0.52/0.71  thf('132', plain, ($false), inference('simplify', [status(thm)], ['131'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
