%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NF25DxWJew

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  142 (1863 expanded)
%              Number of leaves         :   34 ( 637 expanded)
%              Depth                    :   23
%              Number of atoms          :  978 (16121 expanded)
%              Number of equality atoms :  108 (1737 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('4',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X56 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('9',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('49',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','52'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','58','61','62'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('79',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','35'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('85',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('86',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['87','94'])).

thf('96',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['84','95'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('97',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','98'])).

thf('100',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','98'])).

thf('101',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('102',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k5_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['25','99','100','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NF25DxWJew
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 665 iterations in 0.204s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(t2_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['0', '1'])).
% 0.45/0.65  thf(t17_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.45/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.65  thf('4', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(d1_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X54 @ X55)
% 0.45/0.65          | (r2_hidden @ X54 @ X56)
% 0.45/0.65          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X54 : $i, X55 : $i]:
% 0.45/0.65         ((r2_hidden @ X54 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X54 @ X55))),
% 0.45/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.65  thf('7', plain, ((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.65  thf(t1_zfmisc_1, axiom,
% 0.45/0.65    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.45/0.65  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.65  thf('9', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf(t100_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X11 @ X12)
% 0.45/0.65           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('13', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf(t48_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.65           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.65           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('22', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf(t4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.45/0.65          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '24'])).
% 0.45/0.65  thf(t49_zfmisc_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(commutativity_k5_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf(t94_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ A @ B ) =
% 0.45/0.65       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.65           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.45/0.65              (k3_xboole_0 @ X24 @ X25)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.45/0.65              (k5_xboole_0 @ X24 @ X25)))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.45/0.65              (k5_xboole_0 @ X24 @ X25)))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['31', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['26', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.45/0.65              (k5_xboole_0 @ X24 @ X25)))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.45/0.65              (k5_xboole_0 @ X24 @ X25)))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k5_xboole_0 @ 
% 0.45/0.65              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.45/0.65              (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.45/0.65              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.45/0.65         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.45/0.65            (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['36', '41'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf('44', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.45/0.65         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65            (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['42', '45'])).
% 0.45/0.65  thf(t7_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.45/0.65         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65            (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['42', '45'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.45/0.65          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X0 @ 
% 0.45/0.65             (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65              (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.45/0.65          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65               (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.65  thf(l97_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i]:
% 0.45/0.65         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.45/0.65  thf('52', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ~ (r2_hidden @ X0 @ 
% 0.45/0.65            (k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65             (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['47', '52'])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      (((k1_xboole_0)
% 0.45/0.65         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65            (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['46', '53'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '30'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 0.45/0.65         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.45/0.65            (k5_xboole_0 @ (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65             (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.45/0.65         (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['47', '52'])).
% 0.45/0.65  thf(t91_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.45/0.65           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X11 @ X12)
% 0.45/0.65           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['59', '60'])).
% 0.45/0.65  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (((k1_xboole_0)
% 0.45/0.65         = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.45/0.65      inference('demod', [status(thm)], ['56', '57', '58', '61', '62'])).
% 0.45/0.65  thf(t92_xboole_1, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('64', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.45/0.65           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.65           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['64', '65'])).
% 0.45/0.65  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.45/0.65         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['63', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['43', '44'])).
% 0.45/0.65  thf('72', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.45/0.65           = (k3_xboole_0 @ X16 @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.45/0.65         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.65  thf('75', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf('77', plain, (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X0 @ X1)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '30'])).
% 0.45/0.65  thf('79', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.45/0.65         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['77', '78'])).
% 0.45/0.65  thf('80', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['26', '35'])).
% 0.45/0.65  thf('81', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('83', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.45/0.65  thf('84', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.45/0.65  thf(t69_enumset1, axiom,
% 0.45/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.45/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.65  thf(l51_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      (![X59 : $i, X60 : $i]:
% 0.45/0.65         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.45/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.65  thf('87', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['85', '86'])).
% 0.45/0.65  thf('88', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X24 @ X25)
% 0.45/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.45/0.65              (k5_xboole_0 @ X24 @ X25)))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X0 @ X0)
% 0.45/0.65           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.45/0.65  thf('91', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['90', '91'])).
% 0.45/0.65  thf('93', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.65  thf('95', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['87', '94'])).
% 0.45/0.65  thf('96', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['84', '95'])).
% 0.45/0.65  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.65  thf('97', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.45/0.65  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['96', '97'])).
% 0.45/0.65  thf('99', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['83', '98'])).
% 0.45/0.65  thf('100', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['83', '98'])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i]:
% 0.45/0.65         (r1_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k5_xboole_0 @ X9 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.45/0.65  thf('103', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (r1_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['101', '102'])).
% 0.45/0.65  thf('104', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('105', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.65      inference('demod', [status(thm)], ['103', '104'])).
% 0.45/0.65  thf('106', plain, ($false),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '99', '100', '105'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
