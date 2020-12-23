%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yXxz2UJ9Ni

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:48 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  149 (1921 expanded)
%              Number of leaves         :   34 ( 679 expanded)
%              Depth                    :   21
%              Number of atoms          : 1025 (15214 expanded)
%              Number of equality atoms :  112 (1772 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
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
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
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
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('46',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['46','47','50','51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('55',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('67',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('71',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','65','68','69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','65','68','69','70'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('82',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','65','68','69','70'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('87',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88','89'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('92',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('93',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('96',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['94','101'])).

thf('103',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['91','102'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('104',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('105',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['90','105'])).

thf('107',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['90','105'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('108',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('109',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['23','106','107','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yXxz2UJ9Ni
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 614 iterations in 0.280s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf(t2_boole, axiom,
% 0.55/0.74    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf(t17_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.55/0.74      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.55/0.74  thf('4', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.55/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.74  thf(d1_zfmisc_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.55/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X54 @ X55)
% 0.55/0.74          | (r2_hidden @ X54 @ X56)
% 0.55/0.74          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 0.55/0.74      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X54 : $i, X55 : $i]:
% 0.55/0.74         ((r2_hidden @ X54 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X54 @ X55))),
% 0.55/0.74      inference('simplify', [status(thm)], ['5'])).
% 0.55/0.74  thf('7', plain, ((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['4', '6'])).
% 0.55/0.74  thf(t1_zfmisc_1, axiom,
% 0.55/0.74    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.55/0.74  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.55/0.74  thf('9', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.74  thf(t100_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X8 : $i, X9 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X8 @ X9)
% 0.55/0.74           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.55/0.74  thf(t5_boole, axiom,
% 0.55/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.74  thf('13', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.74  thf(t36_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.55/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.74  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.74  thf(t28_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i]:
% 0.55/0.74         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.74  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf(t4_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.55/0.74          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['18', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['9', '22'])).
% 0.55/0.74  thf(t49_zfmisc_1, conjecture,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i]:
% 0.55/0.74        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf(t94_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ A @ B ) =
% 0.55/0.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.55/0.74              (k3_xboole_0 @ X24 @ X25)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.55/0.74              (k5_xboole_0 @ X24 @ X25)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['25', '28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.55/0.74              (k5_xboole_0 @ X24 @ X25)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['30', '31'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['29', '32'])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['24', '33'])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.55/0.74              (k5_xboole_0 @ X24 @ X25)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.55/0.74              (k5_xboole_0 @ X24 @ X25)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.55/0.74           = (k5_xboole_0 @ 
% 0.55/0.74              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.55/0.74              (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.55/0.74           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.55/0.74              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.55/0.74      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.55/0.74         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.55/0.74            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['34', '39'])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('42', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.55/0.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['40', '43'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['25', '28'])).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.55/0.74         = (k5_xboole_0 @ 
% 0.55/0.74            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.55/0.74            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['44', '45'])).
% 0.55/0.74  thf(t91_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.55/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.55/0.74  thf('47', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.55/0.74           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      (![X8 : $i, X9 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X8 @ X9)
% 0.55/0.74           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('50', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X0 @ X1)
% 0.55/0.74           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['48', '49'])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('52', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.55/0.74           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.55/0.74  thf('53', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.55/0.74         = (k5_xboole_0 @ sk_B @ 
% 0.55/0.74            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.55/0.74             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.55/0.74      inference('demod', [status(thm)], ['46', '47', '50', '51', '52'])).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf(t92_xboole_1, axiom,
% 0.55/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.55/0.74  thf('55', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.55/0.74  thf('56', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.55/0.74           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.55/0.74  thf('57', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.55/0.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['55', '56'])).
% 0.55/0.74  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('59', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('60', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['54', '59'])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (((sk_B)
% 0.55/0.74         = (k5_xboole_0 @ 
% 0.55/0.74            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.55/0.74             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.55/0.74            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.55/0.74             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['53', '60'])).
% 0.55/0.74  thf('62', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.55/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.55/0.74           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.55/0.74  thf('63', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('64', plain,
% 0.55/0.74      (![X8 : $i, X9 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X8 @ X9)
% 0.55/0.74           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('65', plain,
% 0.55/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.55/0.74  thf('66', plain,
% 0.55/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.55/0.74  thf('67', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.55/0.74  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['66', '67'])).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('71', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['61', '62', '65', '68', '69', '70'])).
% 0.55/0.74  thf('72', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.55/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.74  thf('73', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i]:
% 0.55/0.74         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.74  thf('74', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.55/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['72', '73'])).
% 0.55/0.74  thf('75', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('76', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.55/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('demod', [status(thm)], ['74', '75'])).
% 0.55/0.74  thf('77', plain,
% 0.55/0.74      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.55/0.74         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['71', '76'])).
% 0.55/0.74  thf('78', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('79', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['61', '62', '65', '68', '69', '70'])).
% 0.55/0.74  thf('80', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.55/0.74  thf('81', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X0 @ X1)
% 0.55/0.74           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['48', '49'])).
% 0.55/0.74  thf('82', plain,
% 0.55/0.74      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.55/0.74         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['80', '81'])).
% 0.55/0.74  thf('83', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['61', '62', '65', '68', '69', '70'])).
% 0.55/0.74  thf('84', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.74  thf('85', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.55/0.74  thf('86', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('87', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['85', '86'])).
% 0.55/0.74  thf('88', plain,
% 0.55/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.55/0.74  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['66', '67'])).
% 0.55/0.74  thf('90', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.55/0.74  thf('91', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.55/0.74  thf(t69_enumset1, axiom,
% 0.55/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.55/0.74  thf('92', plain,
% 0.55/0.74      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.74  thf(l51_zfmisc_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.74  thf('93', plain,
% 0.55/0.74      (![X59 : $i, X60 : $i]:
% 0.55/0.74         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.55/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.55/0.74  thf('94', plain,
% 0.55/0.74      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['92', '93'])).
% 0.55/0.74  thf('95', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('96', plain,
% 0.55/0.74      (![X24 : $i, X25 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X24 @ X25)
% 0.55/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.55/0.74              (k5_xboole_0 @ X24 @ X25)))),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('97', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X0 @ X0)
% 0.55/0.74           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['95', '96'])).
% 0.55/0.74  thf('98', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.55/0.74  thf('99', plain,
% 0.55/0.74      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['97', '98'])).
% 0.55/0.74  thf('100', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.74  thf('102', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['94', '101'])).
% 0.55/0.74  thf('103', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.55/0.74      inference('sup+', [status(thm)], ['91', '102'])).
% 0.55/0.74  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.55/0.74  thf('104', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.55/0.74  thf('105', plain, (((sk_A) = (k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['103', '104'])).
% 0.55/0.74  thf('106', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['90', '105'])).
% 0.55/0.74  thf('107', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['90', '105'])).
% 0.55/0.74  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.55/0.74  thf('108', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.55/0.74  thf('109', plain,
% 0.55/0.74      (![X4 : $i, X5 : $i]:
% 0.55/0.74         ((r1_xboole_0 @ X4 @ X5)
% 0.55/0.74          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.74  thf('110', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.74  thf('111', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['109', '110'])).
% 0.55/0.74  thf('112', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.55/0.74      inference('sup-', [status(thm)], ['108', '111'])).
% 0.55/0.74  thf('113', plain, ($false),
% 0.55/0.74      inference('demod', [status(thm)], ['23', '106', '107', '112'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
