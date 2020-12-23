%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tb04dWgra1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:57 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 224 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  747 (1752 expanded)
%              Number of equality atoms :   90 ( 221 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(t52_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('8',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k3_xboole_0 @ X57 @ ( k1_tarski @ X56 ) )
        = ( k1_tarski @ X56 ) )
      | ~ ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 )
        = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      = sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16','19'])).

thf('21',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,
    ( ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_A @ X0 )
        = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_A @ X0 )
        = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('35',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 != X52 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('36',plain,(
    ! [X52: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X52 ) )
     != ( k1_tarski @ X52 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('38',plain,(
    ! [X55: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X55 ) )
      = X55 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X52: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X52 ) ) ),
    inference(demod,[status(thm)],['36','53'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','56'])).

thf('58',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('59',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('68',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','56','67'])).

thf('69',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['58','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tb04dWgra1
% 0.13/0.37  % Computer   : n019.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:17:38 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 133 iterations in 0.073s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(t65_zfmisc_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.37/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i]:
% 0.37/0.56        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.37/0.56          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.37/0.56        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.37/0.56       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(commutativity_k5_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(t92_xboole_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.56  thf('5', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (((r2_hidden @ sk_B @ sk_A)
% 0.37/0.56        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['6'])).
% 0.37/0.56  thf(t52_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.56       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X56 : $i, X57 : $i]:
% 0.37/0.56         (((k3_xboole_0 @ X57 @ (k1_tarski @ X56)) = (k1_tarski @ X56))
% 0.37/0.56          | ~ (r2_hidden @ X56 @ X57))),
% 0.37/0.56      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      ((((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B)))
% 0.37/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf(t100_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X4 @ X5)
% 0.37/0.56           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.37/0.56          = (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf(t91_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.56           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ X0)
% 0.37/0.56            = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0))))
% 0.37/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ 
% 0.37/0.56          (k1_tarski @ sk_B)) = (k5_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.37/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['5', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf(t5_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.56  thf('18', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.56  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.37/0.56          (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))) = (sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['14', '15', '16', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((((k5_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (sk_A)))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['4', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      ((((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.56           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((k5_xboole_0 @ sk_A @ X0)
% 0.37/0.56            = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0))))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      ((![X0 : $i]:
% 0.37/0.56          ((k5_xboole_0 @ sk_A @ X0)
% 0.37/0.56            = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_B)))))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['3', '25'])).
% 0.37/0.56  thf('27', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.56           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((((k1_tarski @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['26', '31'])).
% 0.37/0.56  thf('33', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf(t20_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.56         ( k1_tarski @ A ) ) <=>
% 0.37/0.56       ( ( A ) != ( B ) ) ))).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X52 : $i, X53 : $i]:
% 0.37/0.56         (((X53) != (X52))
% 0.37/0.56          | ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X52))
% 0.37/0.56              != (k1_tarski @ X53)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X52 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X52))
% 0.37/0.56           != (k1_tarski @ X52))),
% 0.37/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.56  thf(t69_enumset1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf(t31_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.37/0.56  thf('38', plain, (![X55 : $i]: ((k3_tarski @ (k1_tarski @ X55)) = (X55))),
% 0.37/0.56      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.37/0.56  thf('39', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf(l51_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X50 : $i, X51 : $i]:
% 0.37/0.56         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.37/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.56  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf(t95_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k3_xboole_0 @ A @ B ) =
% 0.37/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ X18 @ X19)
% 0.37/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.37/0.56              (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ X18 @ X19)
% 0.37/0.56           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 0.37/0.56              (k5_xboole_0 @ X18 @ X19)))),
% 0.37/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k3_xboole_0 @ X0 @ X0)
% 0.37/0.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['41', '44'])).
% 0.37/0.56  thf('46', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.56  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X4 @ X5)
% 0.37/0.56           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.56  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['51', '52'])).
% 0.37/0.56  thf('54', plain, (![X52 : $i]: ((k1_xboole_0) != (k1_tarski @ X52))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.56         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.56             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['34', '54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.37/0.56       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.37/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.37/0.56  thf('57', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['2', '56'])).
% 0.37/0.56  thf('58', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.37/0.56  thf(l27_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X48 : $i, X49 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.37/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.56  thf(t88_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.56       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13) = (X12))
% 0.37/0.56          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.37/0.56  thf(t40_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.37/0.56           = (k4_xboole_0 @ X6 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.37/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ X1)
% 0.37/0.56          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '64'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.37/0.56         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['6'])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.37/0.56       ((r2_hidden @ sk_B @ sk_A))),
% 0.37/0.56      inference('split', [status(esa)], ['6'])).
% 0.37/0.56  thf('68', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['2', '56', '67'])).
% 0.37/0.56  thf('69', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.37/0.56  thf('70', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['65', '69'])).
% 0.37/0.56  thf('71', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.37/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.37/0.56  thf('72', plain, ($false), inference('demod', [status(thm)], ['58', '71'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
