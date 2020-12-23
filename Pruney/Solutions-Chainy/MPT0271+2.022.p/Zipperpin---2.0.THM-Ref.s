%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYuAR2jlLT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 193 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  629 (1385 expanded)
%              Number of equality atoms :   78 ( 184 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ X19 )
      | ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['21'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X21 @ ( k1_tarski @ X20 ) )
        = ( k1_tarski @ X20 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('44',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYuAR2jlLT
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:14:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 228 iterations in 0.097s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(t68_zfmisc_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.56       ( r2_hidden @ A @ B ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.56          ( r2_hidden @ A @ B ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.20/0.56        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.20/0.56       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf(t48_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf(t4_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf(t100_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf(t5_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('9', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.56  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf(t98_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ X13 @ X14)
% 0.20/0.56           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('17', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.56  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf(t7_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.56  thf(l27_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ (k1_tarski @ X18) @ X19) | (r2_hidden @ X18 @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B_1)
% 0.20/0.56        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.20/0.56          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.20/0.56          = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf(t4_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.56          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.56          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.56           | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r2_hidden @ sk_A @ sk_B_1)
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['20', '32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1)))
% 0.20/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B_1)) & 
% 0.20/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf(t49_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]:
% 0.20/0.56         ((k2_xboole_0 @ (k1_tarski @ X22) @ X23) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B_1)) & 
% 0.20/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_A @ sk_B_1)) & 
% 0.20/0.56             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.20/0.56       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.20/0.56       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('split', [status(esa)], ['21'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['21'])).
% 0.20/0.56  thf(l31_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.56       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X21 @ (k1_tarski @ X20)) = (k1_tarski @ X20))
% 0.20/0.56          | ~ (r2_hidden @ X20 @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.20/0.56          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['44', '47'])).
% 0.20/0.56  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.56           = (k3_xboole_0 @ X9 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('53', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['53', '54'])).
% 0.20/0.56  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.56  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.56         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['48', '57'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_xboole_0)))
% 0.20/0.56         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.56         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))) & 
% 0.20/0.56             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.20/0.56       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.56  thf('62', plain, ($false),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '61'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
