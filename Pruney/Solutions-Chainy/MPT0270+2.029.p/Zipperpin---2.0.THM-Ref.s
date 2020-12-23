%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GpPCj5farp

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:15 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  162 (1126 expanded)
%              Number of leaves         :   22 ( 354 expanded)
%              Depth                    :   26
%              Number of atoms          : 1353 (9661 expanded)
%              Number of equality atoms :  116 ( 775 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('27',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
        = X0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ( ( k4_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
       != ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','49'])).

thf('51',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k4_xboole_0 @ X52 @ ( k1_tarski @ X53 ) )
        = X52 )
      | ( r2_hidden @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','17'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','74'])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('90',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k4_xboole_0 @ X52 @ ( k1_tarski @ X53 ) )
        = X52 )
      | ( r2_hidden @ X53 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('91',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,
    ( ( r1_tarski @ sk_B @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('96',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_B )
      = sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('100',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_B )
      = sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('102',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      = sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['60','63'])).

thf('104',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('106',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['89','106'])).

thf('108',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) )
        = X0 )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_B ) )
        = X0 )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ X0 )
        = X0 )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
        = ( k5_xboole_0 @ X0 @ X0 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','48'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('133',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('134',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','48','133'])).

thf('135',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('136',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['131','135'])).

thf('137',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['50','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GpPCj5farp
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:55:48 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.66/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.84  % Solved by: fo/fo7.sh
% 0.66/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.84  % done 843 iterations in 0.384s
% 0.66/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.84  % SZS output start Refutation
% 0.66/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.66/0.84  thf(t67_zfmisc_1, conjecture,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.66/0.84       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.66/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.84    (~( ![A:$i,B:$i]:
% 0.66/0.84        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.66/0.84          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.66/0.84    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.66/0.84  thf('0', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.66/0.84        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('1', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('split', [status(esa)], ['0'])).
% 0.66/0.84  thf('2', plain,
% 0.66/0.84      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.66/0.84       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.66/0.84      inference('split', [status(esa)], ['0'])).
% 0.66/0.84  thf('3', plain,
% 0.66/0.84      (((r2_hidden @ sk_A @ sk_B)
% 0.66/0.84        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('4', plain,
% 0.66/0.84      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('split', [status(esa)], ['3'])).
% 0.66/0.84  thf(t3_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.66/0.84            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.66/0.84       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.66/0.84            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.66/0.84  thf('5', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i]:
% 0.66/0.84         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X13))),
% 0.66/0.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.66/0.84  thf('6', plain,
% 0.66/0.84      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('split', [status(esa)], ['0'])).
% 0.66/0.84  thf(t36_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.66/0.84  thf('7', plain,
% 0.66/0.84      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.66/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.84  thf('8', plain,
% 0.66/0.84      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup+', [status(thm)], ['6', '7'])).
% 0.66/0.84  thf(t28_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.84  thf('9', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.84  thf('10', plain,
% 0.66/0.84      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.66/0.84          = (k1_tarski @ sk_A)))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.84  thf(t100_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.84  thf('11', plain,
% 0.66/0.84      (![X16 : $i, X17 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X16 @ X17)
% 0.66/0.84           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.84  thf(t1_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.66/0.84       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.66/0.84  thf('12', plain,
% 0.66/0.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X8 @ X9)
% 0.66/0.84          | ~ (r2_hidden @ X8 @ X10)
% 0.66/0.84          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.66/0.84  thf('13', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X2 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.84  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.84  thf('14', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf(d4_xboole_0, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.66/0.84       ( ![D:$i]:
% 0.66/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.66/0.84           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.66/0.84  thf('15', plain,
% 0.66/0.84      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X6 @ X5)
% 0.66/0.84          | (r2_hidden @ X6 @ X4)
% 0.66/0.84          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.84      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.66/0.84  thf('16', plain,
% 0.66/0.84      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.66/0.84         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['15'])).
% 0.66/0.84  thf('17', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['14', '16'])).
% 0.66/0.84  thf('18', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('clc', [status(thm)], ['13', '17'])).
% 0.66/0.84  thf('19', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.66/0.84           | ~ (r2_hidden @ X0 @ 
% 0.66/0.84                (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['10', '18'])).
% 0.66/0.84  thf('20', plain,
% 0.66/0.84      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('split', [status(esa)], ['0'])).
% 0.66/0.84  thf(t48_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.66/0.84  thf('21', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('22', plain,
% 0.66/0.84      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.66/0.84          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup+', [status(thm)], ['20', '21'])).
% 0.66/0.84  thf('23', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf('24', plain,
% 0.66/0.84      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.66/0.84          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('demod', [status(thm)], ['22', '23'])).
% 0.66/0.84  thf('25', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.66/0.84           | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('demod', [status(thm)], ['19', '24'])).
% 0.66/0.84  thf('26', plain,
% 0.66/0.84      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.66/0.84         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['15'])).
% 0.66/0.84  thf('27', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('clc', [status(thm)], ['25', '26'])).
% 0.66/0.84  thf('28', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['5', '27'])).
% 0.66/0.84  thf(t83_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.84  thf('29', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.66/0.84      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.66/0.84  thf('30', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.66/0.84            = (X0)))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['28', '29'])).
% 0.66/0.84  thf('31', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('32', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('33', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.84           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['31', '32'])).
% 0.66/0.84  thf('34', plain,
% 0.66/0.84      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.66/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.84  thf('35', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.84  thf('36', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.66/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.66/0.84  thf('37', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf('38', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.84  thf('39', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['33', '38'])).
% 0.66/0.84  thf('40', plain,
% 0.66/0.84      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup+', [status(thm)], ['30', '39'])).
% 0.66/0.84  thf(t79_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.66/0.84  thf('41', plain,
% 0.66/0.84      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.66/0.84      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.66/0.84  thf('42', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.66/0.84      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.66/0.84  thf('43', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['41', '42'])).
% 0.66/0.84  thf(t65_zfmisc_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.66/0.84       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.66/0.84  thf('44', plain,
% 0.66/0.84      (![X51 : $i, X52 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X51 @ X52)
% 0.66/0.84          | ((k4_xboole_0 @ X52 @ (k1_tarski @ X51)) != (X52)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.84  thf('45', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.66/0.84            != (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.66/0.84          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.66/0.84  thf('46', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['45'])).
% 0.66/0.84  thf('47', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_A @ sk_B))
% 0.66/0.84         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['40', '46'])).
% 0.66/0.84  thf('48', plain,
% 0.66/0.84      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.66/0.84       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.66/0.84      inference('sup-', [status(thm)], ['4', '47'])).
% 0.66/0.84  thf('49', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.66/0.84      inference('sat_resolution*', [status(thm)], ['2', '48'])).
% 0.66/0.84  thf('50', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.66/0.84      inference('simpl_trail', [status(thm)], ['1', '49'])).
% 0.66/0.84  thf('51', plain,
% 0.66/0.84      (![X52 : $i, X53 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X52 @ (k1_tarski @ X53)) = (X52))
% 0.66/0.84          | (r2_hidden @ X53 @ X52))),
% 0.66/0.84      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.84  thf('52', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('53', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.66/0.84          | (r2_hidden @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['51', '52'])).
% 0.66/0.84  thf('54', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i]:
% 0.66/0.84         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X13))),
% 0.66/0.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.66/0.84  thf('55', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.84           = (k4_xboole_0 @ X1 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['41', '42'])).
% 0.66/0.84  thf('56', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.84  thf('57', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf('58', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('clc', [status(thm)], ['13', '17'])).
% 0.66/0.84  thf('59', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['57', '58'])).
% 0.66/0.84  thf('60', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['56', '59'])).
% 0.66/0.84  thf('61', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.84  thf('62', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['14', '16'])).
% 0.66/0.84  thf('63', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['61', '62'])).
% 0.66/0.84  thf('64', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.66/0.84      inference('clc', [status(thm)], ['60', '63'])).
% 0.66/0.84  thf('65', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['55', '64'])).
% 0.66/0.84  thf('66', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['54', '65'])).
% 0.66/0.84  thf('67', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.66/0.84      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.66/0.84  thf('68', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.66/0.84  thf('69', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('70', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['68', '69'])).
% 0.66/0.84  thf('71', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf('72', plain,
% 0.66/0.84      (![X16 : $i, X17 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X16 @ X17)
% 0.66/0.84           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.84  thf('73', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['71', '72'])).
% 0.66/0.84  thf('74', plain,
% 0.66/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['70', '73'])).
% 0.66/0.84  thf('75', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.66/0.84          | (r2_hidden @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['53', '74'])).
% 0.66/0.84  thf('76', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i]:
% 0.66/0.84         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 0.66/0.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.66/0.84  thf('77', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['55', '64'])).
% 0.66/0.84  thf('78', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.66/0.84      inference('sup-', [status(thm)], ['76', '77'])).
% 0.66/0.84  thf('79', plain,
% 0.66/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['70', '73'])).
% 0.66/0.84  thf('80', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.66/0.84      inference('demod', [status(thm)], ['78', '79'])).
% 0.66/0.84  thf('81', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.66/0.84      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.66/0.84  thf('82', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 0.66/0.84           = (k5_xboole_0 @ X1 @ X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['80', '81'])).
% 0.66/0.84  thf('83', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('84', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ X0 @ X0)
% 0.66/0.84           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['82', '83'])).
% 0.66/0.84  thf('85', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.84  thf('86', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.66/0.84           = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['84', '85'])).
% 0.66/0.84  thf('87', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k5_xboole_0 @ X0 @ X0)
% 0.66/0.84           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['82', '83'])).
% 0.66/0.84  thf('88', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['86', '87'])).
% 0.66/0.84  thf('89', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i]:
% 0.66/0.84         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X13))),
% 0.66/0.84      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.66/0.84  thf('90', plain,
% 0.66/0.84      (![X52 : $i, X53 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X52 @ (k1_tarski @ X53)) = (X52))
% 0.66/0.84          | (r2_hidden @ X53 @ X52))),
% 0.66/0.84      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.66/0.84  thf('91', plain,
% 0.66/0.84      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.66/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.84  thf('92', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X0) | (r2_hidden @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['90', '91'])).
% 0.66/0.84  thf('93', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('split', [status(esa)], ['0'])).
% 0.66/0.84  thf('94', plain,
% 0.66/0.84      (((r1_tarski @ sk_B @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['92', '93'])).
% 0.66/0.84  thf('95', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.84  thf('96', plain,
% 0.66/0.84      ((((k3_xboole_0 @ sk_B @ sk_B) = (sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['94', '95'])).
% 0.66/0.84  thf('97', plain,
% 0.66/0.84      (![X16 : $i, X17 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X16 @ X17)
% 0.66/0.84           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.84  thf('98', plain,
% 0.66/0.84      ((((k4_xboole_0 @ sk_B @ sk_B) = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['96', '97'])).
% 0.66/0.84  thf('99', plain,
% 0.66/0.84      (![X22 : $i, X23 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.66/0.84           = (k3_xboole_0 @ X22 @ X23))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf('100', plain,
% 0.66/0.84      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 0.66/0.84          = (k3_xboole_0 @ sk_B @ sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['98', '99'])).
% 0.66/0.84  thf('101', plain,
% 0.66/0.84      ((((k3_xboole_0 @ sk_B @ sk_B) = (sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['94', '95'])).
% 0.66/0.84  thf('102', plain,
% 0.66/0.84      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)) = (sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('demod', [status(thm)], ['100', '101'])).
% 0.66/0.84  thf('103', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.66/0.84      inference('clc', [status(thm)], ['60', '63'])).
% 0.66/0.84  thf('104', plain,
% 0.66/0.84      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['102', '103'])).
% 0.66/0.84  thf('105', plain,
% 0.66/0.84      ((((k4_xboole_0 @ sk_B @ sk_B) = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['96', '97'])).
% 0.66/0.84  thf('106', plain,
% 0.66/0.84      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('demod', [status(thm)], ['104', '105'])).
% 0.66/0.84  thf('107', plain,
% 0.66/0.84      ((![X0 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['89', '106'])).
% 0.66/0.84  thf('108', plain,
% 0.66/0.84      (![X26 : $i, X27 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 0.66/0.84      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.66/0.84  thf('109', plain,
% 0.66/0.84      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) = (X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['107', '108'])).
% 0.66/0.84  thf('110', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.84  thf('111', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          ((k3_xboole_0 @ X0 @ X0)
% 0.66/0.84            = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B))))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['109', '110'])).
% 0.66/0.84  thf('112', plain,
% 0.66/0.84      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_B)) = (X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['107', '108'])).
% 0.66/0.84  thf('113', plain,
% 0.66/0.84      ((![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('demod', [status(thm)], ['111', '112'])).
% 0.66/0.84  thf('114', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['71', '72'])).
% 0.66/0.84  thf('115', plain,
% 0.66/0.84      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['113', '114'])).
% 0.66/0.84  thf('116', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.66/0.84  thf('117', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.66/0.84            = (k4_xboole_0 @ X0 @ X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['115', '116'])).
% 0.66/0.84  thf('118', plain,
% 0.66/0.84      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['113', '114'])).
% 0.66/0.84  thf('119', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.66/0.84            = (k5_xboole_0 @ X0 @ X0)))
% 0.66/0.84         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.66/0.84      inference('demod', [status(thm)], ['117', '118'])).
% 0.66/0.84  thf('120', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.66/0.84      inference('sat_resolution*', [status(thm)], ['2', '48'])).
% 0.66/0.84  thf('121', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.66/0.84           = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 0.66/0.84  thf('122', plain,
% 0.66/0.84      (![X16 : $i, X17 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X16 @ X17)
% 0.66/0.84           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.84  thf('123', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['121', '122'])).
% 0.66/0.84  thf('124', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.66/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.66/0.84  thf('125', plain,
% 0.66/0.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['70', '73'])).
% 0.66/0.84  thf('126', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['124', '125'])).
% 0.66/0.84  thf('127', plain,
% 0.66/0.84      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['123', '126'])).
% 0.66/0.84  thf('128', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['88', '127'])).
% 0.66/0.84  thf('129', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         (((X2) = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))
% 0.66/0.84          | (r2_hidden @ X0 @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['75', '128'])).
% 0.66/0.84  thf('130', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['71', '72'])).
% 0.66/0.84  thf('131', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.66/0.84          | (r2_hidden @ X0 @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['129', '130'])).
% 0.66/0.84  thf('132', plain,
% 0.66/0.84      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.66/0.84         <= (~
% 0.66/0.84             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.66/0.84      inference('split', [status(esa)], ['3'])).
% 0.66/0.84  thf('133', plain,
% 0.66/0.84      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.66/0.84       ((r2_hidden @ sk_A @ sk_B))),
% 0.66/0.84      inference('split', [status(esa)], ['3'])).
% 0.66/0.84  thf('134', plain,
% 0.66/0.84      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.66/0.84      inference('sat_resolution*', [status(thm)], ['2', '48', '133'])).
% 0.66/0.84  thf('135', plain,
% 0.66/0.84      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.66/0.84      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 0.66/0.84  thf('136', plain,
% 0.66/0.84      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.66/0.84      inference('sup-', [status(thm)], ['131', '135'])).
% 0.66/0.84  thf('137', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.66/0.84      inference('simplify', [status(thm)], ['136'])).
% 0.66/0.84  thf('138', plain, ($false), inference('demod', [status(thm)], ['50', '137'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
