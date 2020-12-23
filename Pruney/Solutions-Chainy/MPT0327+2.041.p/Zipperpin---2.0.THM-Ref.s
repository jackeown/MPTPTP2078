%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rh7QBod95d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:55 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 379 expanded)
%              Number of leaves         :   24 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  761 (2884 expanded)
%              Number of equality atoms :   77 ( 319 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

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

thf('10',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['42','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('63',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('70',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['31','70'])).

thf('72',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rh7QBod95d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.53  % Solved by: fo/fo7.sh
% 0.33/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.53  % done 233 iterations in 0.081s
% 0.33/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.53  % SZS output start Refutation
% 0.33/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.33/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.33/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.53  thf(d10_xboole_0, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.53  thf('0', plain,
% 0.33/0.53      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.53  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.33/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.33/0.53  thf(t28_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.33/0.53  thf('2', plain,
% 0.33/0.53      (![X10 : $i, X11 : $i]:
% 0.33/0.53         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.33/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.33/0.53  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.53  thf(t100_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.53  thf('4', plain,
% 0.33/0.53      (![X8 : $i, X9 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X8 @ X9)
% 0.33/0.53           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.33/0.53  thf('6', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.33/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.33/0.53  thf(l32_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.33/0.53  thf('7', plain,
% 0.33/0.53      (![X5 : $i, X7 : $i]:
% 0.33/0.53         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.33/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.33/0.53  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.33/0.53  thf('9', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '8'])).
% 0.33/0.53  thf(t140_zfmisc_1, conjecture,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.33/0.53       ( ( k2_xboole_0 @
% 0.33/0.53           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.33/0.53         ( B ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i,B:$i]:
% 0.33/0.53        ( ( r2_hidden @ A @ B ) =>
% 0.33/0.53          ( ( k2_xboole_0 @
% 0.33/0.53              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.33/0.53            ( B ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.33/0.53  thf('10', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(l1_zfmisc_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      (![X36 : $i, X38 : $i]:
% 0.33/0.53         ((r1_tarski @ (k1_tarski @ X36) @ X38) | ~ (r2_hidden @ X36 @ X38))),
% 0.33/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.33/0.53  thf('12', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.33/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.33/0.53  thf('13', plain,
% 0.33/0.53      (![X10 : $i, X11 : $i]:
% 0.33/0.53         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.33/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.33/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.33/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.33/0.53  thf('15', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.33/0.53  thf('17', plain,
% 0.33/0.53      (![X8 : $i, X9 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X8 @ X9)
% 0.33/0.53           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('18', plain,
% 0.33/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.33/0.53  thf(t91_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i,C:$i]:
% 0.33/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.33/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.33/0.53  thf('19', plain,
% 0.33/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.33/0.53           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.33/0.53  thf('20', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.33/0.53           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.33/0.53  thf('21', plain,
% 0.33/0.53      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['9', '20'])).
% 0.33/0.53  thf(t5_boole, axiom,
% 0.33/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.33/0.53  thf('22', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.33/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.33/0.53  thf('23', plain,
% 0.33/0.53      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A)) = (sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('24', plain,
% 0.33/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.33/0.53           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.33/0.53  thf('25', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ sk_B @ X0)
% 0.33/0.53           = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.33/0.53  thf(t94_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k2_xboole_0 @ A @ B ) =
% 0.33/0.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.53  thf('26', plain,
% 0.33/0.53      (![X24 : $i, X25 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X24 @ X25)
% 0.33/0.53           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.33/0.53              (k3_xboole_0 @ X24 @ X25)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.33/0.53  thf('27', plain,
% 0.33/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.33/0.53           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.33/0.53  thf('28', plain,
% 0.33/0.53      (![X24 : $i, X25 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X24 @ X25)
% 0.33/0.53           = (k5_xboole_0 @ X24 @ 
% 0.33/0.53              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.33/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.33/0.53  thf('29', plain,
% 0.33/0.53      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ 
% 0.33/0.53            (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53             (k1_tarski @ sk_A))))),
% 0.33/0.53      inference('sup+', [status(thm)], ['25', '28'])).
% 0.33/0.53  thf('30', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.33/0.53  thf('31', plain,
% 0.33/0.53      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ 
% 0.33/0.53            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.33/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.33/0.53  thf('32', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.33/0.53  thf('33', plain,
% 0.33/0.53      (![X8 : $i, X9 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X8 @ X9)
% 0.33/0.53           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('34', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X0 @ X1)
% 0.33/0.53           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.33/0.53  thf('35', plain,
% 0.33/0.53      (![X8 : $i, X9 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X8 @ X9)
% 0.33/0.53           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('36', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.33/0.53           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.33/0.53  thf('37', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53           (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.33/0.53           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.33/0.53  thf('38', plain,
% 0.33/0.53      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ 
% 0.33/0.53            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.33/0.53      inference('sup+', [status(thm)], ['34', '37'])).
% 0.33/0.53  thf(t79_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.33/0.53  thf('39', plain,
% 0.33/0.53      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.33/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.33/0.53  thf(t83_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.33/0.53  thf('40', plain,
% 0.33/0.53      (![X18 : $i, X19 : $i]:
% 0.33/0.53         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.33/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.33/0.53  thf('41', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.33/0.53           = (k4_xboole_0 @ X1 @ X0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.33/0.53  thf('42', plain,
% 0.33/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ 
% 0.33/0.53            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.33/0.53      inference('demod', [status(thm)], ['38', '41'])).
% 0.33/0.53  thf('43', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '8'])).
% 0.33/0.53  thf('44', plain,
% 0.33/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.33/0.53           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.33/0.53  thf('45', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['43', '44'])).
% 0.33/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.33/0.53  thf('46', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.33/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.33/0.53  thf('47', plain,
% 0.33/0.53      (![X10 : $i, X11 : $i]:
% 0.33/0.53         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.33/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.33/0.53  thf('48', plain,
% 0.33/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.33/0.53  thf('49', plain,
% 0.33/0.53      (![X24 : $i, X25 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X24 @ X25)
% 0.33/0.53           = (k5_xboole_0 @ X24 @ 
% 0.33/0.53              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.33/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.33/0.53  thf('50', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.53           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.33/0.53  thf('51', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.33/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.33/0.53  thf('52', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.33/0.53  thf('53', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['45', '52'])).
% 0.33/0.53  thf('54', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '8'])).
% 0.33/0.53  thf('55', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.33/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['45', '52'])).
% 0.33/0.53  thf('56', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['54', '55'])).
% 0.33/0.53  thf('57', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.33/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.33/0.53  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['56', '57'])).
% 0.33/0.53  thf('59', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['53', '58'])).
% 0.33/0.53  thf('60', plain,
% 0.33/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.33/0.53      inference('sup+', [status(thm)], ['42', '59'])).
% 0.33/0.53  thf('61', plain,
% 0.33/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.33/0.53  thf('62', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['53', '58'])).
% 0.33/0.53  thf('63', plain,
% 0.33/0.53      (((k1_tarski @ sk_A)
% 0.33/0.53         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.33/0.53      inference('sup+', [status(thm)], ['61', '62'])).
% 0.33/0.53  thf('64', plain,
% 0.33/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['60', '63'])).
% 0.33/0.53  thf('65', plain,
% 0.33/0.53      (![X8 : $i, X9 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X8 @ X9)
% 0.33/0.53           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('66', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ sk_B @ X0)
% 0.33/0.53           = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.33/0.53  thf('67', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.33/0.53           = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53              (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['65', '66'])).
% 0.33/0.53  thf('68', plain,
% 0.33/0.53      (((k5_xboole_0 @ sk_B @ 
% 0.33/0.53         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.33/0.53         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53            (k1_tarski @ sk_A)))),
% 0.33/0.53      inference('sup+', [status(thm)], ['64', '67'])).
% 0.33/0.53  thf('69', plain,
% 0.33/0.53      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A)) = (sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('70', plain,
% 0.33/0.53      (((k5_xboole_0 @ sk_B @ 
% 0.33/0.53         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.33/0.53          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.33/0.53         = (sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['68', '69'])).
% 0.33/0.53  thf('71', plain,
% 0.33/0.53      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A)) = (sk_B))),
% 0.33/0.53      inference('sup+', [status(thm)], ['31', '70'])).
% 0.33/0.53  thf('72', plain,
% 0.33/0.53      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.33/0.53         (k1_tarski @ sk_A)) != (sk_B))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('73', plain, ($false),
% 0.33/0.53      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.33/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
