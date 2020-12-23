%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U4T7AwZMGi

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 309 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  880 (2631 expanded)
%              Number of equality atoms :   85 ( 291 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X48 @ X49 ) )
      = ( k2_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,
    ( ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,
    ( ( ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('33',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X52 @ X51 )
      | ~ ( r1_tarski @ ( k2_tarski @ X50 @ X52 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['45'])).

thf('49',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    ! [X50: $i,X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X50 @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r2_hidden @ X50 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('55',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('59',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('63',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['45'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf('73',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ ( k2_tarski @ X50 @ X52 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('74',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['45'])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','70','71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U4T7AwZMGi
% 0.13/0.36  % Computer   : n012.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:11:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 539 iterations in 0.281s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(t73_zfmisc_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.73       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.73        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.73          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      (((r2_hidden @ sk_B @ sk_C)
% 0.54/0.73        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.73       ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (((r2_hidden @ sk_A @ sk_C)
% 0.54/0.73        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 0.54/0.73         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.73      inference('split', [status(esa)], ['2'])).
% 0.54/0.73  thf(t95_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k3_xboole_0 @ A @ B ) =
% 0.54/0.73       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X17 @ X18)
% 0.54/0.73           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.54/0.73              (k2_xboole_0 @ X17 @ X18)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.54/0.73  thf(t91_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.73       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.54/0.73           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X17 @ X18)
% 0.54/0.73           = (k5_xboole_0 @ X17 @ 
% 0.54/0.73              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.54/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf(t92_xboole_1, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.73  thf('7', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.73         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.54/0.73           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf(commutativity_k5_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.73  thf(t5_boole, axiom,
% 0.54/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.73  thf('11', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.54/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.73  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['6', '13'])).
% 0.54/0.73  thf(t100_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X5 : $i, X6 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X5 @ X6)
% 0.54/0.73           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.73           = (k4_xboole_0 @ X1 @ X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k2_xboole_0 @ X1 @ X0)
% 0.54/0.73           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          = (k5_xboole_0 @ sk_C @ k1_xboole_0)))
% 0.54/0.73         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.73      inference('sup+', [status(thm)], ['3', '18'])).
% 0.54/0.73  thf(commutativity_k2_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X19 : $i, X20 : $i]:
% 0.54/0.73         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.54/0.73  thf(l51_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X48 : $i, X49 : $i]:
% 0.54/0.73         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.54/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['20', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X48 : $i, X49 : $i]:
% 0.54/0.73         ((k3_tarski @ (k2_tarski @ X48 @ X49)) = (k2_xboole_0 @ X48 @ X49))),
% 0.54/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.73  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      ((((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (sk_C)))
% 0.54/0.73         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.73      inference('demod', [status(thm)], ['19', '24', '25', '26'])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.73           = (k4_xboole_0 @ X1 @ X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      ((((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.73          = (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.73         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      ((((k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.73          = (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.73         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      ((((k2_tarski @ sk_A @ sk_B)
% 0.54/0.74          = (k5_xboole_0 @ sk_C @ 
% 0.54/0.74             (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))
% 0.54/0.74         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('sup+', [status(thm)], ['31', '32'])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (![X5 : $i, X6 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X5 @ X6)
% 0.54/0.74           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.74  thf('36', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k3_xboole_0 @ X1 @ X0)
% 0.54/0.74           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['34', '35'])).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      ((((k2_tarski @ sk_A @ sk_B)
% 0.54/0.74          = (k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.74         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('demod', [status(thm)], ['33', '36'])).
% 0.54/0.74  thf(d10_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.74  thf('38', plain,
% 0.54/0.74      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.54/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.74  thf('39', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.54/0.74      inference('simplify', [status(thm)], ['38'])).
% 0.54/0.74  thf(t18_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.74         ((r1_tarski @ X9 @ X10)
% 0.54/0.74          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.54/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.74  thf('42', plain,
% 0.54/0.74      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.54/0.74         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('sup+', [status(thm)], ['37', '41'])).
% 0.54/0.74  thf(t38_zfmisc_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.54/0.74       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.54/0.74  thf('43', plain,
% 0.54/0.74      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.54/0.74         ((r2_hidden @ X52 @ X51)
% 0.54/0.74          | ~ (r1_tarski @ (k2_tarski @ X50 @ X52) @ X51))),
% 0.54/0.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.54/0.74  thf('44', plain,
% 0.54/0.74      (((r2_hidden @ sk_B @ sk_C))
% 0.54/0.74         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.74  thf('45', plain,
% 0.54/0.74      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.54/0.74        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.54/0.74        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('46', plain,
% 0.54/0.74      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('split', [status(esa)], ['45'])).
% 0.54/0.74  thf('47', plain,
% 0.54/0.74      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.74       ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['44', '46'])).
% 0.54/0.74  thf('48', plain,
% 0.54/0.74      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.54/0.74       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.74       ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.74      inference('split', [status(esa)], ['45'])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('split', [status(esa)], ['0'])).
% 0.54/0.74  thf('50', plain,
% 0.54/0.74      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.54/0.74      inference('split', [status(esa)], ['2'])).
% 0.54/0.74  thf('51', plain,
% 0.54/0.74      (![X50 : $i, X52 : $i, X53 : $i]:
% 0.54/0.74         ((r1_tarski @ (k2_tarski @ X50 @ X52) @ X53)
% 0.54/0.74          | ~ (r2_hidden @ X52 @ X53)
% 0.54/0.74          | ~ (r2_hidden @ X50 @ X53))),
% 0.54/0.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.54/0.74  thf('52', plain,
% 0.54/0.74      ((![X0 : $i]:
% 0.54/0.74          (~ (r2_hidden @ X0 @ sk_C)
% 0.54/0.74           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C)))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.74  thf('53', plain,
% 0.54/0.74      (((r1_tarski @ (k2_tarski @ sk_B @ sk_A) @ sk_C))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['49', '52'])).
% 0.54/0.74  thf('54', plain,
% 0.54/0.74      (![X19 : $i, X20 : $i]:
% 0.54/0.74         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.54/0.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.54/0.74  thf('55', plain,
% 0.54/0.74      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['53', '54'])).
% 0.54/0.74  thf(t12_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.74  thf('56', plain,
% 0.54/0.74      (![X7 : $i, X8 : $i]:
% 0.54/0.74         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.54/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.74  thf('57', plain,
% 0.54/0.74      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C)))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['55', '56'])).
% 0.54/0.74  thf('58', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i]:
% 0.54/0.74         ((k3_xboole_0 @ X17 @ X18)
% 0.54/0.74           = (k5_xboole_0 @ X17 @ 
% 0.54/0.74              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.54/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.54/0.74  thf('59', plain,
% 0.54/0.74      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.74          = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.54/0.74             (k5_xboole_0 @ sk_C @ sk_C))))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['57', '58'])).
% 0.54/0.74  thf('60', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.74  thf('61', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.74  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf('63', plain,
% 0.54/0.74      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.74          = (k2_tarski @ sk_A @ sk_B)))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (![X5 : $i, X6 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X5 @ X6)
% 0.54/0.74           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.74          = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.54/0.74             (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.54/0.74  thf('66', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.54/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.74  thf('67', plain,
% 0.54/0.74      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 0.54/0.74         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['65', '66'])).
% 0.54/0.74  thf('68', plain,
% 0.54/0.74      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('split', [status(esa)], ['45'])).
% 0.54/0.74  thf('69', plain,
% 0.54/0.74      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) & 
% 0.54/0.74             ((r2_hidden @ sk_A @ sk_C)) & 
% 0.54/0.74             ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['67', '68'])).
% 0.54/0.74  thf('70', plain,
% 0.54/0.74      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.74       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.74      inference('simplify', [status(thm)], ['69'])).
% 0.54/0.74  thf('71', plain,
% 0.54/0.74      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.74       ((r2_hidden @ sk_A @ sk_C))),
% 0.54/0.74      inference('split', [status(esa)], ['2'])).
% 0.54/0.74  thf('72', plain,
% 0.54/0.74      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.54/0.74         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('sup+', [status(thm)], ['37', '41'])).
% 0.54/0.74  thf('73', plain,
% 0.54/0.74      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.54/0.74         ((r2_hidden @ X50 @ X51)
% 0.54/0.74          | ~ (r1_tarski @ (k2_tarski @ X50 @ X52) @ X51))),
% 0.54/0.74      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.54/0.74  thf('74', plain,
% 0.54/0.74      (((r2_hidden @ sk_A @ sk_C))
% 0.54/0.74         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['72', '73'])).
% 0.54/0.74  thf('75', plain,
% 0.54/0.74      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.54/0.74      inference('split', [status(esa)], ['45'])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.74       ((r2_hidden @ sk_A @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.74  thf('77', plain, ($false),
% 0.54/0.74      inference('sat_resolution*', [status(thm)],
% 0.54/0.74                ['1', '47', '48', '70', '71', '76'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
