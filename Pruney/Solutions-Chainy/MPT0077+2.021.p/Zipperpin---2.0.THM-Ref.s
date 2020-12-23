%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VlpjVsyAKy

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:52 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 282 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  831 (2673 expanded)
%              Number of equality atoms :   52 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['28'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('39',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','25','44'])).

thf('46',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('68',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','77'])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_A )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','85'])).

thf('87',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_A )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('90',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['27','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VlpjVsyAKy
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 1444 iterations in 0.603s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.05  thf(t70_xboole_1, conjecture,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.84/1.05            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.84/1.05       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.84/1.05            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.05        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.84/1.05               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.84/1.05          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.84/1.05               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.84/1.05  thf('0', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 0.84/1.05        | ~ (r1_xboole_0 @ sk_A @ sk_B_1)
% 0.84/1.05        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('1', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.84/1.05         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('split', [status(esa)], ['0'])).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))) | 
% 0.84/1.05       ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.84/1.05      inference('split', [status(esa)], ['0'])).
% 0.84/1.05  thf('3', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.84/1.05        | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('4', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('split', [status(esa)], ['3'])).
% 0.84/1.05  thf(symmetry_r1_xboole_0, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X2 : $i, X3 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.84/1.05      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.05  thf(t7_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.05  thf(t63_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.84/1.05       ( r1_xboole_0 @ A @ C ) ))).
% 0.84/1.05  thf('8', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X18 @ X19)
% 0.84/1.05          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.84/1.05          | (r1_xboole_0 @ X18 @ X20))),
% 0.84/1.05      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X1 @ X2)
% 0.84/1.05          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_B_1 @ sk_A))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['6', '9'])).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (![X2 : $i, X3 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.84/1.05      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.05  thf('13', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.84/1.05      inference('split', [status(esa)], ['0'])).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.84/1.05       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['12', '13'])).
% 0.84/1.05  thf('15', plain,
% 0.84/1.05      (((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.05  thf(commutativity_k2_xboole_0, axiom,
% 0.84/1.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.05  thf('17', plain,
% 0.84/1.05      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['16', '17'])).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.84/1.05         (~ (r1_tarski @ X18 @ X19)
% 0.84/1.05          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.84/1.05          | (r1_xboole_0 @ X18 @ X20))),
% 0.84/1.05      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.84/1.05  thf('20', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X0 @ X2)
% 0.84/1.05          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['18', '19'])).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_C_1 @ sk_A))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['15', '20'])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      (![X2 : $i, X3 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.84/1.05      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['21', '22'])).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.84/1.05      inference('split', [status(esa)], ['0'])).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.84/1.05       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['23', '24'])).
% 0.84/1.05  thf('26', plain,
% 0.84/1.05      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.84/1.05      inference('sat_resolution*', [status(thm)], ['2', '14', '25'])).
% 0.84/1.05  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.84/1.05  thf('28', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.84/1.05        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.84/1.05      inference('split', [status(esa)], ['28'])).
% 0.84/1.05  thf(t7_xboole_0, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.84/1.05          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.84/1.05  thf('30', plain,
% 0.84/1.05      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.84/1.05      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.84/1.05  thf(t4_xboole_0, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.05            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.84/1.05  thf('31', plain,
% 0.84/1.05      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.84/1.05          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.84/1.05  thf('32', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['30', '31'])).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['29', '32'])).
% 0.84/1.05  thf('34', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.84/1.05       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.84/1.05      inference('split', [status(esa)], ['28'])).
% 0.84/1.05  thf('35', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.05      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '34'])).
% 0.84/1.05  thf('36', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.84/1.05  thf('37', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.84/1.05      inference('split', [status(esa)], ['3'])).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['30', '31'])).
% 0.84/1.05  thf('39', plain,
% 0.84/1.05      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['37', '38'])).
% 0.84/1.05  thf(t47_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      (![X14 : $i, X15 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.84/1.05           = (k4_xboole_0 @ X14 @ X15))),
% 0.84/1.05      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1)))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['39', '40'])).
% 0.84/1.05  thf(t3_boole, axiom,
% 0.84/1.05    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.05  thf('42', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.84/1.05  thf('43', plain,
% 0.84/1.05      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1)))
% 0.84/1.05         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['41', '42'])).
% 0.84/1.05  thf('44', plain,
% 0.84/1.05      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.84/1.05       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.84/1.05      inference('split', [status(esa)], ['3'])).
% 0.84/1.05  thf('45', plain, (((r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.84/1.05      inference('sat_resolution*', [status(thm)], ['2', '14', '25', '44'])).
% 0.84/1.05  thf('46', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.84/1.05      inference('simpl_trail', [status(thm)], ['43', '45'])).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.05  thf(t41_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i,C:$i]:
% 0.84/1.05     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.84/1.05       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.84/1.05  thf('48', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.84/1.05           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.84/1.05  thf('49', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.84/1.05           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['47', '48'])).
% 0.84/1.05  thf('50', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.84/1.05           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.84/1.05           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['49', '50'])).
% 0.84/1.05  thf('52', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ sk_A @ X0)
% 0.84/1.05           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['46', '51'])).
% 0.84/1.05  thf('53', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.84/1.05           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.84/1.05  thf(t48_xboole_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.84/1.05  thf('54', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.84/1.05           = (k3_xboole_0 @ X16 @ X17))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('55', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.84/1.05           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['53', '54'])).
% 0.84/1.05  thf('56', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.84/1.05           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['52', '55'])).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.84/1.05           = (k3_xboole_0 @ X16 @ X17))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('58', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ sk_A @ X0)
% 0.84/1.05           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.84/1.05      inference('demod', [status(thm)], ['56', '57'])).
% 0.84/1.05  thf('59', plain,
% 0.84/1.05      (![X4 : $i, X5 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X4 @ X5)
% 0.84/1.05          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.84/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.84/1.05  thf('60', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.84/1.05           = (k3_xboole_0 @ X16 @ X17))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('61', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.84/1.05  thf('62', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.84/1.05           = (k3_xboole_0 @ X16 @ X17))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('63', plain,
% 0.84/1.05      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['61', '62'])).
% 0.84/1.05  thf(t2_boole, axiom,
% 0.84/1.05    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.84/1.05  thf('64', plain,
% 0.84/1.05      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.05      inference('cnf', [status(esa)], [t2_boole])).
% 0.84/1.05  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.05      inference('demod', [status(thm)], ['63', '64'])).
% 0.84/1.05  thf('66', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.84/1.05           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['49', '50'])).
% 0.84/1.05  thf('67', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ k1_xboole_0 @ X1)
% 0.84/1.05           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['65', '66'])).
% 0.84/1.05  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.84/1.05  thf('68', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 0.84/1.05      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.84/1.05  thf('69', plain,
% 0.84/1.05      (![X2 : $i, X3 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.84/1.05      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.84/1.05  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.84/1.05      inference('sup-', [status(thm)], ['68', '69'])).
% 0.84/1.05  thf('71', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['30', '31'])).
% 0.84/1.05  thf('72', plain,
% 0.84/1.05      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.84/1.05      inference('sup-', [status(thm)], ['70', '71'])).
% 0.84/1.05  thf('73', plain,
% 0.84/1.05      (![X14 : $i, X15 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.84/1.05           = (k4_xboole_0 @ X14 @ X15))),
% 0.84/1.05      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.84/1.05  thf('74', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.84/1.05           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['72', '73'])).
% 0.84/1.05  thf('75', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.84/1.05  thf('76', plain,
% 0.84/1.05      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['74', '75'])).
% 0.84/1.05  thf('77', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['67', '76'])).
% 0.84/1.05  thf('78', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.84/1.05      inference('sup+', [status(thm)], ['60', '77'])).
% 0.84/1.05  thf('79', plain,
% 0.84/1.05      (![X16 : $i, X17 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.84/1.05           = (k3_xboole_0 @ X16 @ X17))),
% 0.84/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.84/1.05  thf('80', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.84/1.05           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.84/1.05      inference('sup+', [status(thm)], ['78', '79'])).
% 0.84/1.05  thf('81', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.84/1.05  thf('82', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((k3_xboole_0 @ X0 @ X1)
% 0.84/1.05           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.84/1.05      inference('demod', [status(thm)], ['80', '81'])).
% 0.84/1.05  thf('83', plain,
% 0.84/1.05      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.84/1.05          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.84/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.84/1.05  thf('84', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.84/1.05          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['82', '83'])).
% 0.84/1.05  thf('85', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X1 @ X0)
% 0.84/1.05          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['59', '84'])).
% 0.84/1.05  thf('86', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_A)
% 0.84/1.05          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['58', '85'])).
% 0.84/1.05  thf('87', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ k1_xboole_0 @ sk_A)
% 0.84/1.05        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B_1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['36', '86'])).
% 0.84/1.05  thf('88', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.84/1.05      inference('sup-', [status(thm)], ['68', '69'])).
% 0.84/1.05  thf('89', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.05  thf('90', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.84/1.05      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.84/1.05  thf('91', plain, ($false), inference('demod', [status(thm)], ['27', '90'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
