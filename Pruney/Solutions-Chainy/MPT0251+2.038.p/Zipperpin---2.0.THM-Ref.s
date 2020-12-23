%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KAxbs71sfq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:06 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 202 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  622 (1358 expanded)
%              Number of equality atoms :   61 ( 153 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X41 @ X42 ) )
      = ( k2_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','41'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','62'])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('65',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('67',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('70',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KAxbs71sfq
% 0.13/0.37  % Computer   : n006.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:44:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 500 iterations in 0.153s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.62  thf(d3_tarski, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X1 : $i, X3 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf(t46_zfmisc_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.40/0.62       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i]:
% 0.40/0.62        ( ( r2_hidden @ A @ B ) =>
% 0.40/0.62          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.40/0.62  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(l1_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X38 : $i, X40 : $i]:
% 0.40/0.62         ((r1_tarski @ (k1_tarski @ X38) @ X40) | ~ (r2_hidden @ X38 @ X40))),
% 0.40/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.62  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf(t28_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X16 : $i, X17 : $i]:
% 0.40/0.62         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf(t51_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.40/0.62       ( A ) ))).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X22 : $i, X23 : $i]:
% 0.40/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 0.40/0.62           = (X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.40/0.62         (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) = (k1_tarski @ sk_A))),
% 0.40/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.40/0.62  thf(commutativity_k2_tarski, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X26 : $i, X27 : $i]:
% 0.40/0.62         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.40/0.62  thf(l51_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (![X41 : $i, X42 : $i]:
% 0.40/0.62         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.40/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X41 : $i, X42 : $i]:
% 0.40/0.62         ((k3_tarski @ (k2_tarski @ X41 @ X42)) = (k2_xboole_0 @ X41 @ X42))),
% 0.40/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.62  thf(t7_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.40/0.62        (k1_tarski @ sk_A))),
% 0.40/0.62      inference('sup+', [status(thm)], ['7', '14'])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | (r2_hidden @ X0 @ X2)
% 0.40/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.40/0.62          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf(t100_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X11 @ X12)
% 0.40/0.62           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.62  thf(t1_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.40/0.62       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X4 @ X5)
% 0.40/0.62          | ~ (r2_hidden @ X4 @ X6)
% 0.40/0.62          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.40/0.62          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.62          | ~ (r2_hidden @ X2 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.62  thf(t22_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i]:
% 0.40/0.62         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 0.40/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.40/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | (r2_hidden @ X0 @ X2)
% 0.40/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.62          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.40/0.62      inference('clc', [status(thm)], ['21', '26'])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.40/0.62          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '27'])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.40/0.62      inference('clc', [status(thm)], ['17', '28'])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '29'])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.62  thf(t1_boole, axiom,
% 0.40/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.62  thf('32', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.40/0.62  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf(t40_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      (![X20 : $i, X21 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.40/0.62           = (k4_xboole_0 @ X20 @ X21))),
% 0.40/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf(d10_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.62  thf('37', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.40/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.40/0.62  thf('38', plain,
% 0.40/0.62      (![X16 : $i, X17 : $i]:
% 0.40/0.62         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.40/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.62  thf('39', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.62  thf('40', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X11 @ X12)
% 0.40/0.62           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['39', '40'])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['35', '41'])).
% 0.40/0.62  thf(t39_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i]:
% 0.40/0.62         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.40/0.62           = (k2_xboole_0 @ X18 @ X19))),
% 0.40/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.40/0.62  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('45', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.40/0.62  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i]:
% 0.40/0.62         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 0.40/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.40/0.62  thf('50', plain,
% 0.40/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['48', '49'])).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X11 @ X12)
% 0.40/0.62           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.62  thf('52', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.62           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.62           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('54', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['52', '53'])).
% 0.40/0.62  thf('55', plain,
% 0.40/0.62      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['47', '54'])).
% 0.40/0.62  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['42', '55'])).
% 0.40/0.62  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('58', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.62  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.40/0.62  thf('60', plain,
% 0.40/0.62      (![X8 : $i, X10 : $i]:
% 0.40/0.62         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.62  thf('61', plain,
% 0.40/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.62  thf('62', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['56', '61'])).
% 0.40/0.62  thf('63', plain,
% 0.40/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['30', '62'])).
% 0.40/0.62  thf('64', plain,
% 0.40/0.62      (![X18 : $i, X19 : $i]:
% 0.40/0.62         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.40/0.62           = (k2_xboole_0 @ X18 @ X19))),
% 0.40/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.40/0.62  thf('65', plain,
% 0.40/0.62      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.40/0.62         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['63', '64'])).
% 0.40/0.62  thf('66', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.40/0.62  thf('67', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.62  thf('68', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('69', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.62  thf('70', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['68', '69'])).
% 0.40/0.62  thf('71', plain, ($false),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['67', '70'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
