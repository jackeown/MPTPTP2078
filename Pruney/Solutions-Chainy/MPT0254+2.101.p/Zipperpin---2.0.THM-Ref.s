%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ac7C9eKHZA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:49 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  155 (2251 expanded)
%              Number of leaves         :   34 ( 797 expanded)
%              Depth                    :   24
%              Number of atoms          : 1100 (17854 expanded)
%              Number of equality atoms :  119 (2103 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ X52 @ X53 )
      | ( r2_hidden @ X52 @ X54 )
      | ( X54
       != ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ~ ( r1_tarski @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
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

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','47','48'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

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
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
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
    inference('sup+',[status(thm)],['37','38'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('72',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','62','65','68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('77',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('86',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('88',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('91',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('93',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('96',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94','95'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('98',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('99',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('102',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['100','107'])).

thf('109',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['97','108'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('110',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','111'])).

thf('113',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','111'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('114',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('115',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['19','112','113','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ac7C9eKHZA
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 440 iterations in 0.233s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.68  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(t1_zfmisc_1, axiom,
% 0.49/0.68    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.49/0.68  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.49/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.68  thf('1', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.68  thf(d1_zfmisc_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.49/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X52 @ X53)
% 0.49/0.68          | (r2_hidden @ X52 @ X54)
% 0.49/0.68          | ((X54) != (k1_zfmisc_1 @ X53)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X52 : $i, X53 : $i]:
% 0.49/0.68         ((r2_hidden @ X52 @ (k1_zfmisc_1 @ X53)) | ~ (r1_tarski @ X52 @ X53))),
% 0.49/0.68      inference('simplify', [status(thm)], ['2'])).
% 0.49/0.68  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '3'])).
% 0.49/0.68  thf('5', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['0', '4'])).
% 0.49/0.68  thf(t2_boole, axiom,
% 0.49/0.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.68  thf(t100_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (![X8 : $i, X9 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf(t5_boole, axiom,
% 0.49/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.68  thf('9', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.49/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.68  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf(t36_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.49/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.68  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.49/0.68  thf(t28_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (![X10 : $i, X11 : $i]:
% 0.49/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.68  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.68  thf(t4_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.49/0.68          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.68          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['14', '17'])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ (k1_tarski @ k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['5', '18'])).
% 0.49/0.68  thf(t49_zfmisc_1, conjecture,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i,B:$i]:
% 0.49/0.68        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(commutativity_k5_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf(t94_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k2_xboole_0 @ A @ B ) =
% 0.49/0.68       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X22 @ X23)
% 0.49/0.68           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.49/0.68              (k3_xboole_0 @ X22 @ X23)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('24', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X22 @ X23)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.49/0.68              (k5_xboole_0 @ X22 @ X23)))),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['21', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X22 @ X23)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.49/0.68              (k5_xboole_0 @ X22 @ X23)))),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['25', '28'])).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['20', '29'])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X22 @ X23)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.49/0.68              (k5_xboole_0 @ X22 @ X23)))),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X22 @ X23)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.49/0.68              (k5_xboole_0 @ X22 @ X23)))),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.49/0.68           = (k5_xboole_0 @ 
% 0.49/0.68              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.49/0.68              (k2_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['31', '32'])).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.49/0.68           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.49/0.68              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.49/0.68      inference('demod', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.49/0.68         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.49/0.68            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['30', '35'])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('38', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.49/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.68  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.49/0.68         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.49/0.68      inference('demod', [status(thm)], ['36', '39'])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['21', '24'])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.49/0.68         = (k5_xboole_0 @ 
% 0.49/0.68            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.49/0.68            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['40', '41'])).
% 0.49/0.68  thf(t91_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.49/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.49/0.68           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (![X8 : $i, X9 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['44', '45'])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.49/0.68           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.49/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.49/0.68            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.49/0.68             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.49/0.68      inference('demod', [status(thm)], ['42', '43', '46', '47', '48'])).
% 0.49/0.68  thf(t92_xboole_1, axiom,
% 0.49/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.49/0.68  thf('50', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.49/0.68           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.49/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['50', '51'])).
% 0.49/0.68  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('54', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      (((k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.49/0.68         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.49/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.49/0.68            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['49', '54'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.49/0.68           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.68  thf('57', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.49/0.68           = (k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['56', '57'])).
% 0.49/0.68  thf('59', plain,
% 0.49/0.68      (((k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.49/0.68         (k5_xboole_0 @ 
% 0.49/0.68          (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68           (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.49/0.68          (k5_xboole_0 @ sk_B @ 
% 0.49/0.68           (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.49/0.68            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))
% 0.49/0.68         = (k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['55', '58'])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.49/0.68           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.49/0.68  thf('61', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.49/0.68           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['60', '61'])).
% 0.49/0.68  thf('63', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('64', plain,
% 0.49/0.68      (![X8 : $i, X9 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.49/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.68  thf('65', plain,
% 0.49/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['63', '64'])).
% 0.49/0.68  thf('66', plain,
% 0.49/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['63', '64'])).
% 0.49/0.68  thf('67', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.49/0.68  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['66', '67'])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('71', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('72', plain,
% 0.49/0.68      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.49/0.68         = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)],
% 0.49/0.68                ['59', '62', '65', '68', '69', '70', '71'])).
% 0.49/0.68  thf('73', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.49/0.68  thf('74', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.49/0.68         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['72', '73'])).
% 0.49/0.68  thf('75', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('77', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.49/0.68  thf('78', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.49/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.68  thf('79', plain,
% 0.49/0.68      (![X10 : $i, X11 : $i]:
% 0.49/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.68  thf('80', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.49/0.68           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.68  thf('81', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.68  thf('82', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.49/0.68           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['80', '81'])).
% 0.49/0.68  thf('83', plain,
% 0.49/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['77', '82'])).
% 0.49/0.68  thf('84', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.68  thf('85', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.49/0.68  thf('86', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.49/0.68  thf('87', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['44', '45'])).
% 0.49/0.68  thf('88', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.49/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['86', '87'])).
% 0.49/0.68  thf('89', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.49/0.68  thf('90', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.49/0.68  thf('91', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.49/0.68  thf('92', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.49/0.68  thf('93', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['91', '92'])).
% 0.49/0.68  thf('94', plain,
% 0.49/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['63', '64'])).
% 0.49/0.68  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['66', '67'])).
% 0.49/0.68  thf('96', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.49/0.68  thf('97', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.49/0.68  thf(t69_enumset1, axiom,
% 0.49/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.49/0.68  thf('98', plain,
% 0.49/0.68      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.49/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.68  thf(l51_zfmisc_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.68  thf('99', plain,
% 0.49/0.68      (![X57 : $i, X58 : $i]:
% 0.49/0.68         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.49/0.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.49/0.68  thf('100', plain,
% 0.49/0.68      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['98', '99'])).
% 0.49/0.68  thf('101', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('102', plain,
% 0.49/0.68      (![X22 : $i, X23 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X22 @ X23)
% 0.49/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.49/0.68              (k5_xboole_0 @ X22 @ X23)))),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('103', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((k2_xboole_0 @ X0 @ X0)
% 0.49/0.68           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['101', '102'])).
% 0.49/0.68  thf('104', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.49/0.68  thf('105', plain,
% 0.49/0.68      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['103', '104'])).
% 0.49/0.68  thf('106', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.49/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.49/0.68  thf('107', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['105', '106'])).
% 0.49/0.68  thf('108', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['100', '107'])).
% 0.49/0.68  thf('109', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['97', '108'])).
% 0.49/0.68  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.49/0.68  thf('110', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.49/0.68  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['109', '110'])).
% 0.49/0.68  thf('112', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['96', '111'])).
% 0.49/0.68  thf('113', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['96', '111'])).
% 0.49/0.68  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.49/0.68  thf('114', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.49/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.68  thf('115', plain,
% 0.49/0.68      (![X4 : $i, X5 : $i]:
% 0.49/0.68         ((r1_xboole_0 @ X4 @ X5)
% 0.49/0.68          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.68  thf('116', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.49/0.68          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.49/0.68  thf('117', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['115', '116'])).
% 0.49/0.68  thf('118', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.68      inference('sup-', [status(thm)], ['114', '117'])).
% 0.49/0.68  thf('119', plain, ($false),
% 0.49/0.68      inference('demod', [status(thm)], ['19', '112', '113', '118'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
