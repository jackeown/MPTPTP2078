%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6tUtKIFqjH

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:49 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 307 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  985 (2908 expanded)
%              Number of equality atoms :   78 ( 124 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','23'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
      = sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C )
   <= ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','23','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('75',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','80'])).

thf('82',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('84',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('86',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('88',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','14','23','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('97',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['40','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['25','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6tUtKIFqjH
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.82/2.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.82/2.00  % Solved by: fo/fo7.sh
% 1.82/2.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.00  % done 2227 iterations in 1.537s
% 1.82/2.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.82/2.00  % SZS output start Refutation
% 1.82/2.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.82/2.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.82/2.00  thf(sk_B_type, type, sk_B: $i).
% 1.82/2.00  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.82/2.00  thf(sk_C_type, type, sk_C: $i).
% 1.82/2.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.82/2.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.82/2.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.82/2.00  thf(t70_xboole_1, conjecture,
% 1.82/2.00    (![A:$i,B:$i,C:$i]:
% 1.82/2.00     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.82/2.00            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.82/2.00       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.82/2.00            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.82/2.00  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.00    (~( ![A:$i,B:$i,C:$i]:
% 1.82/2.00        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.82/2.00               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.82/2.00          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.82/2.00               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 1.82/2.00    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 1.82/2.00  thf('0', plain,
% 1.82/2.00      ((~ (r1_xboole_0 @ sk_A @ sk_C)
% 1.82/2.00        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 1.82/2.00        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.82/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.00  thf('1', plain,
% 1.82/2.00      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.82/2.00         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('split', [status(esa)], ['0'])).
% 1.82/2.00  thf('2', plain,
% 1.82/2.00      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 1.82/2.00       ~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 1.82/2.00      inference('split', [status(esa)], ['0'])).
% 1.82/2.00  thf('3', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.82/2.00        | (r1_xboole_0 @ sk_A @ sk_B))),
% 1.82/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.00  thf('4', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('split', [status(esa)], ['3'])).
% 1.82/2.00  thf(symmetry_r1_xboole_0, axiom,
% 1.82/2.00    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.82/2.00  thf('5', plain,
% 1.82/2.00      (![X7 : $i, X8 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.82/2.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.82/2.00  thf('6', plain,
% 1.82/2.00      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['4', '5'])).
% 1.82/2.00  thf(t7_xboole_1, axiom,
% 1.82/2.00    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.82/2.00  thf('7', plain,
% 1.82/2.00      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.82/2.00      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.82/2.00  thf(t63_xboole_1, axiom,
% 1.82/2.00    (![A:$i,B:$i,C:$i]:
% 1.82/2.00     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.82/2.00       ( r1_xboole_0 @ A @ C ) ))).
% 1.82/2.00  thf('8', plain,
% 1.82/2.00      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.82/2.00         (~ (r1_tarski @ X20 @ X21)
% 1.82/2.00          | ~ (r1_xboole_0 @ X21 @ X22)
% 1.82/2.00          | (r1_xboole_0 @ X20 @ X22))),
% 1.82/2.00      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.82/2.00  thf('9', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X1 @ X2)
% 1.82/2.00          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.82/2.00      inference('sup-', [status(thm)], ['7', '8'])).
% 1.82/2.00  thf('10', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_B @ sk_A))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['6', '9'])).
% 1.82/2.00  thf('11', plain,
% 1.82/2.00      (![X7 : $i, X8 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.82/2.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.82/2.00  thf('12', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_B))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['10', '11'])).
% 1.82/2.00  thf('13', plain,
% 1.82/2.00      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.82/2.00      inference('split', [status(esa)], ['0'])).
% 1.82/2.00  thf('14', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 1.82/2.00       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.00  thf('15', plain,
% 1.82/2.00      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['4', '5'])).
% 1.82/2.00  thf(commutativity_k2_xboole_0, axiom,
% 1.82/2.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.82/2.00  thf('16', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.00  thf('17', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X1 @ X2)
% 1.82/2.00          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.82/2.00      inference('sup-', [status(thm)], ['7', '8'])).
% 1.82/2.00  thf('18', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.82/2.00          | (r1_xboole_0 @ X0 @ X2))),
% 1.82/2.00      inference('sup-', [status(thm)], ['16', '17'])).
% 1.82/2.00  thf('19', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_C @ sk_A))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['15', '18'])).
% 1.82/2.00  thf('20', plain,
% 1.82/2.00      (![X7 : $i, X8 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.82/2.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.82/2.00  thf('21', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_C))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['19', '20'])).
% 1.82/2.00  thf('22', plain,
% 1.82/2.00      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.82/2.00      inference('split', [status(esa)], ['0'])).
% 1.82/2.00  thf('23', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 1.82/2.00       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['21', '22'])).
% 1.82/2.00  thf('24', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.82/2.00      inference('sat_resolution*', [status(thm)], ['2', '14', '23'])).
% 1.82/2.00  thf('25', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.82/2.00      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 1.82/2.00  thf('26', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.82/2.00        | (r1_xboole_0 @ sk_A @ sk_C))),
% 1.82/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.00  thf('27', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_C)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.82/2.00      inference('split', [status(esa)], ['26'])).
% 1.82/2.00  thf('28', plain,
% 1.82/2.00      (![X7 : $i, X8 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.82/2.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.82/2.00  thf('29', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_C @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['27', '28'])).
% 1.82/2.00  thf(d7_xboole_0, axiom,
% 1.82/2.00    (![A:$i,B:$i]:
% 1.82/2.00     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.82/2.00       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.82/2.00  thf('30', plain,
% 1.82/2.00      (![X4 : $i, X5 : $i]:
% 1.82/2.00         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.82/2.00      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.82/2.00  thf('31', plain,
% 1.82/2.00      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['29', '30'])).
% 1.82/2.00  thf(t51_xboole_1, axiom,
% 1.82/2.00    (![A:$i,B:$i]:
% 1.82/2.00     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.82/2.00       ( A ) ))).
% 1.82/2.00  thf('32', plain,
% 1.82/2.00      (![X18 : $i, X19 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 1.82/2.00           = (X18))),
% 1.82/2.00      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.82/2.00  thf('33', plain,
% 1.82/2.00      ((((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C)))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.82/2.00      inference('sup+', [status(thm)], ['31', '32'])).
% 1.82/2.00  thf('34', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.00  thf(t1_boole, axiom,
% 1.82/2.00    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.82/2.00  thf('35', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.82/2.00      inference('cnf', [status(esa)], [t1_boole])).
% 1.82/2.00  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['34', '35'])).
% 1.82/2.00  thf('37', plain,
% 1.82/2.00      ((((k4_xboole_0 @ sk_C @ sk_A) = (sk_C)))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ sk_C)))),
% 1.82/2.00      inference('demod', [status(thm)], ['33', '36'])).
% 1.82/2.00  thf('38', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_C)) | 
% 1.82/2.00       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.82/2.00      inference('split', [status(esa)], ['26'])).
% 1.82/2.00  thf('39', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 1.82/2.00      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '38'])).
% 1.82/2.00  thf('40', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 1.82/2.00      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 1.82/2.00  thf(t3_boole, axiom,
% 1.82/2.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.82/2.00  thf('41', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.82/2.00      inference('cnf', [status(esa)], [t3_boole])).
% 1.82/2.00  thf(t48_xboole_1, axiom,
% 1.82/2.00    (![A:$i,B:$i]:
% 1.82/2.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.82/2.00  thf('42', plain,
% 1.82/2.00      (![X16 : $i, X17 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.82/2.00           = (k3_xboole_0 @ X16 @ X17))),
% 1.82/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.82/2.00  thf('43', plain,
% 1.82/2.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['41', '42'])).
% 1.82/2.00  thf('44', plain,
% 1.82/2.00      (![X18 : $i, X19 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 1.82/2.00           = (X18))),
% 1.82/2.00      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.82/2.00  thf('45', plain,
% 1.82/2.00      (![X0 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.82/2.00           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['43', '44'])).
% 1.82/2.00  thf('46', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.82/2.00      inference('cnf', [status(esa)], [t3_boole])).
% 1.82/2.00  thf('47', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.00  thf(t39_xboole_1, axiom,
% 1.82/2.00    (![A:$i,B:$i]:
% 1.82/2.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.82/2.00  thf('48', plain,
% 1.82/2.00      (![X10 : $i, X11 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.82/2.00           = (k2_xboole_0 @ X10 @ X11))),
% 1.82/2.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.82/2.00  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.82/2.00      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 1.82/2.00  thf('50', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.00  thf(t41_xboole_1, axiom,
% 1.82/2.00    (![A:$i,B:$i,C:$i]:
% 1.82/2.00     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.82/2.00       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.82/2.00  thf('51', plain,
% 1.82/2.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.82/2.00           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.82/2.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.82/2.00  thf('52', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 1.82/2.00           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.82/2.00      inference('sup+', [status(thm)], ['50', '51'])).
% 1.82/2.00  thf('53', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.82/2.00           = (k4_xboole_0 @ X1 @ X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['49', '52'])).
% 1.82/2.00  thf('54', plain,
% 1.82/2.00      (![X16 : $i, X17 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.82/2.00           = (k3_xboole_0 @ X16 @ X17))),
% 1.82/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.82/2.00  thf('55', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.82/2.00           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['53', '54'])).
% 1.82/2.00  thf('56', plain,
% 1.82/2.00      (![X10 : $i, X11 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.82/2.00           = (k2_xboole_0 @ X10 @ X11))),
% 1.82/2.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.82/2.00  thf('57', plain,
% 1.82/2.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.82/2.00           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.82/2.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.82/2.00  thf('58', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 1.82/2.00           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.82/2.00      inference('sup+', [status(thm)], ['56', '57'])).
% 1.82/2.00  thf('59', plain,
% 1.82/2.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.82/2.00           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.82/2.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.82/2.00  thf('60', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 1.82/2.00           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.82/2.00      inference('demod', [status(thm)], ['58', '59'])).
% 1.82/2.00  thf(commutativity_k3_xboole_0, axiom,
% 1.82/2.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.82/2.00  thf('61', plain,
% 1.82/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.00  thf('62', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.82/2.00           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.82/2.00      inference('demod', [status(thm)], ['55', '60', '61'])).
% 1.82/2.00  thf('63', plain,
% 1.82/2.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['41', '42'])).
% 1.82/2.00  thf('64', plain,
% 1.82/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.00  thf('65', plain,
% 1.82/2.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['63', '64'])).
% 1.82/2.00  thf('66', plain,
% 1.82/2.00      (![X16 : $i, X17 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.82/2.00           = (k3_xboole_0 @ X16 @ X17))),
% 1.82/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.82/2.00  thf('67', plain,
% 1.82/2.00      (![X10 : $i, X11 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.82/2.00           = (k2_xboole_0 @ X10 @ X11))),
% 1.82/2.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.82/2.00  thf('68', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.82/2.00           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.82/2.00      inference('sup+', [status(thm)], ['66', '67'])).
% 1.82/2.00  thf('69', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.00  thf('70', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.00  thf('71', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.82/2.00           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.82/2.00      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.82/2.00  thf('72', plain,
% 1.82/2.00      (![X18 : $i, X19 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 1.82/2.00           = (X18))),
% 1.82/2.00      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.82/2.00  thf('73', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 1.82/2.00      inference('sup+', [status(thm)], ['71', '72'])).
% 1.82/2.00  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['34', '35'])).
% 1.82/2.00  thf('75', plain,
% 1.82/2.00      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['73', '74'])).
% 1.82/2.00  thf('76', plain,
% 1.82/2.00      (![X16 : $i, X17 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.82/2.00           = (k3_xboole_0 @ X16 @ X17))),
% 1.82/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.82/2.00  thf('77', plain,
% 1.82/2.00      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['75', '76'])).
% 1.82/2.00  thf('78', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.82/2.00      inference('demod', [status(thm)], ['65', '77'])).
% 1.82/2.00  thf('79', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 1.82/2.00           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.82/2.00      inference('demod', [status(thm)], ['58', '59'])).
% 1.82/2.00  thf('80', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['78', '79'])).
% 1.82/2.00  thf('81', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.82/2.00      inference('demod', [status(thm)], ['62', '80'])).
% 1.82/2.00  thf('82', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.82/2.00      inference('split', [status(esa)], ['3'])).
% 1.82/2.00  thf('83', plain,
% 1.82/2.00      (![X7 : $i, X8 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.82/2.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.82/2.00  thf('84', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_B @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['82', '83'])).
% 1.82/2.00  thf('85', plain,
% 1.82/2.00      (![X4 : $i, X5 : $i]:
% 1.82/2.00         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.82/2.00      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.82/2.00  thf('86', plain,
% 1.82/2.00      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.82/2.00         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['84', '85'])).
% 1.82/2.00  thf('87', plain,
% 1.82/2.00      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 1.82/2.00       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.82/2.00      inference('split', [status(esa)], ['3'])).
% 1.82/2.00  thf('88', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 1.82/2.00      inference('sat_resolution*', [status(thm)], ['2', '14', '23', '87'])).
% 1.82/2.00  thf('89', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.82/2.00      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 1.82/2.00  thf('90', plain,
% 1.82/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.00  thf('91', plain,
% 1.82/2.00      (![X18 : $i, X19 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 1.82/2.00           = (X18))),
% 1.82/2.00      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.82/2.00  thf('92', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i]:
% 1.82/2.00         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.82/2.00           = (X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['90', '91'])).
% 1.82/2.00  thf('93', plain,
% 1.82/2.00      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 1.82/2.00      inference('sup+', [status(thm)], ['89', '92'])).
% 1.82/2.00  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.82/2.00      inference('sup+', [status(thm)], ['34', '35'])).
% 1.82/2.00  thf('95', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.82/2.00      inference('demod', [status(thm)], ['93', '94'])).
% 1.82/2.00  thf('96', plain,
% 1.82/2.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.82/2.00           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.82/2.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.82/2.00  thf('97', plain,
% 1.82/2.00      (![X16 : $i, X17 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.82/2.00           = (k3_xboole_0 @ X16 @ X17))),
% 1.82/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.82/2.00  thf('98', plain,
% 1.82/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 1.82/2.00           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.82/2.00      inference('sup+', [status(thm)], ['96', '97'])).
% 1.82/2.00  thf('99', plain,
% 1.82/2.00      (![X0 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 1.82/2.00           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.82/2.00      inference('sup+', [status(thm)], ['95', '98'])).
% 1.82/2.00  thf('100', plain,
% 1.82/2.00      (![X16 : $i, X17 : $i]:
% 1.82/2.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.82/2.00           = (k3_xboole_0 @ X16 @ X17))),
% 1.82/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.82/2.00  thf('101', plain,
% 1.82/2.00      (![X0 : $i]:
% 1.82/2.00         ((k3_xboole_0 @ sk_A @ X0)
% 1.82/2.00           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.82/2.00      inference('demod', [status(thm)], ['99', '100'])).
% 1.82/2.00  thf('102', plain,
% 1.82/2.00      (![X4 : $i, X6 : $i]:
% 1.82/2.00         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.82/2.00      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.82/2.00  thf('103', plain,
% 1.82/2.00      (![X0 : $i]:
% 1.82/2.00         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 1.82/2.00          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.82/2.00      inference('sup-', [status(thm)], ['101', '102'])).
% 1.82/2.00  thf('104', plain,
% 1.82/2.00      (![X0 : $i]:
% 1.82/2.00         (((k1_xboole_0) != (k1_xboole_0))
% 1.82/2.00          | (r1_xboole_0 @ sk_A @ 
% 1.82/2.00             (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))))),
% 1.82/2.00      inference('sup-', [status(thm)], ['81', '103'])).
% 1.82/2.00  thf('105', plain,
% 1.82/2.00      (![X0 : $i]:
% 1.82/2.00         (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.82/2.00      inference('simplify', [status(thm)], ['104'])).
% 1.82/2.00  thf('106', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.82/2.00      inference('sup+', [status(thm)], ['40', '105'])).
% 1.82/2.00  thf('107', plain, ($false), inference('demod', [status(thm)], ['25', '106'])).
% 1.82/2.00  
% 1.82/2.00  % SZS output end Refutation
% 1.82/2.00  
% 1.82/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
