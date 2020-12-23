%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6v4Z2A7iHZ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:34 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 678 expanded)
%              Number of leaves         :   27 ( 217 expanded)
%              Depth                    :   20
%              Number of atoms          : 1057 (5994 expanded)
%              Number of equality atoms :   55 ( 360 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) @ X22 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X14 @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('46',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ X0 @ sk_A ) ) )
        | ~ ( r2_hidden @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ X0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ sk_C )
        | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('59',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['37','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','61'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','62'])).

thf('64',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','63'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('65',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ( r1_xboole_0 @ ( k2_tarski @ X45 @ X47 ) @ X46 )
      | ( r2_hidden @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('70',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X43 @ X42 )
      | ~ ( r1_tarski @ ( k2_tarski @ X41 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('73',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ( r2_hidden @ X0 @ X3 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) )
        | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ X0 @ sk_B ) ) )
        | ~ ( r2_hidden @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ X0 @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_C )
      | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','88'])).

thf('90',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('91',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','62','89','90'])).

thf('92',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['68','91'])).

thf('93',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['67','92'])).

thf('94',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['95'])).

thf('98',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','62','89','90','97'])).

thf('99',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['96','98'])).

thf('100',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['94','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['64','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6v4Z2A7iHZ
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.84/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.02  % Solved by: fo/fo7.sh
% 0.84/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.02  % done 1684 iterations in 0.570s
% 0.84/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.02  % SZS output start Refutation
% 0.84/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.02  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.84/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.02  thf(t72_zfmisc_1, conjecture,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.84/1.02       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.84/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.02    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.02        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.84/1.02          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 0.84/1.02    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 0.84/1.02  thf('0', plain,
% 0.84/1.02      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.84/1.02        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02            = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('1', plain,
% 0.84/1.02      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['0'])).
% 0.84/1.02  thf('2', plain,
% 0.84/1.02      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.84/1.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('split', [status(esa)], ['0'])).
% 0.84/1.02  thf(t7_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.02  thf('3', plain,
% 0.84/1.02      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.84/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.02  thf(t43_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.84/1.02       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.84/1.02  thf('4', plain,
% 0.84/1.02      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.84/1.02         ((r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.84/1.02          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.84/1.02  thf('5', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.84/1.02      inference('sup-', [status(thm)], ['3', '4'])).
% 0.84/1.02  thf(t38_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.84/1.02       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.84/1.02  thf('6', plain,
% 0.84/1.02      (![X4 : $i, X5 : $i]:
% 0.84/1.02         (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.84/1.02  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.02  thf(t90_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.84/1.02  thf('8', plain,
% 0.84/1.02      (![X21 : $i, X22 : $i]:
% 0.84/1.02         (r1_xboole_0 @ (k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)) @ X22)),
% 0.84/1.02      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.84/1.02  thf(t47_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.02  thf('9', plain,
% 0.84/1.02      (![X9 : $i, X10 : $i]:
% 0.84/1.02         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.84/1.02           = (k4_xboole_0 @ X9 @ X10))),
% 0.84/1.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.84/1.02  thf('10', plain,
% 0.84/1.02      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.84/1.02      inference('demod', [status(thm)], ['8', '9'])).
% 0.84/1.02  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.84/1.02      inference('sup+', [status(thm)], ['7', '10'])).
% 0.84/1.02  thf(t81_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.84/1.02       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.84/1.02  thf('12', plain,
% 0.84/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.84/1.02         ((r1_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.84/1.02          | ~ (r1_xboole_0 @ X14 @ (k4_xboole_0 @ X13 @ X15)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.84/1.02  thf('13', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]:
% 0.84/1.02         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['11', '12'])).
% 0.84/1.02  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.02  thf('15', plain,
% 0.84/1.02      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.84/1.02      inference('demod', [status(thm)], ['8', '9'])).
% 0.84/1.02  thf(t83_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.02  thf('16', plain,
% 0.84/1.02      (![X18 : $i, X19 : $i]:
% 0.84/1.02         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.84/1.02      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.84/1.02  thf('17', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]:
% 0.84/1.02         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.84/1.02           = (k4_xboole_0 @ X1 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.02  thf('18', plain,
% 0.84/1.02      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.84/1.02      inference('sup+', [status(thm)], ['14', '17'])).
% 0.84/1.02  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.02  thf('20', plain,
% 0.84/1.02      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.84/1.02      inference('demod', [status(thm)], ['18', '19'])).
% 0.84/1.02  thf('21', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.84/1.02      inference('demod', [status(thm)], ['13', '20'])).
% 0.84/1.02  thf('22', plain,
% 0.84/1.02      (![X18 : $i, X19 : $i]:
% 0.84/1.02         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.84/1.02      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.84/1.02  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['21', '22'])).
% 0.84/1.02  thf(commutativity_k2_tarski, axiom,
% 0.84/1.02    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.84/1.02  thf('24', plain,
% 0.84/1.02      (![X32 : $i, X33 : $i]:
% 0.84/1.02         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 0.84/1.02      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.02  thf(l51_zfmisc_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.02  thf('25', plain,
% 0.84/1.02      (![X37 : $i, X38 : $i]:
% 0.84/1.02         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.84/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.84/1.02  thf('26', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]:
% 0.84/1.02         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.02      inference('sup+', [status(thm)], ['24', '25'])).
% 0.84/1.02  thf('27', plain,
% 0.84/1.02      (![X37 : $i, X38 : $i]:
% 0.84/1.02         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.84/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.84/1.02  thf('28', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.02      inference('sup+', [status(thm)], ['26', '27'])).
% 0.84/1.02  thf('29', plain,
% 0.84/1.02      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.84/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.02  thf('30', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.84/1.02      inference('sup+', [status(thm)], ['28', '29'])).
% 0.84/1.02  thf('31', plain,
% 0.84/1.02      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.84/1.02         ((r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.84/1.02          | ~ (r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.84/1.02  thf('32', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.84/1.02      inference('sup-', [status(thm)], ['30', '31'])).
% 0.84/1.02  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.84/1.02      inference('sup+', [status(thm)], ['23', '32'])).
% 0.84/1.02  thf(t38_zfmisc_1, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.84/1.02       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.84/1.02  thf('34', plain,
% 0.84/1.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.84/1.02         ((r2_hidden @ X41 @ X42)
% 0.84/1.02          | ~ (r1_tarski @ (k2_tarski @ X41 @ X43) @ X42))),
% 0.84/1.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.84/1.02  thf('35', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.02  thf('36', plain,
% 0.84/1.02      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))))),
% 0.84/1.02      inference('split', [status(esa)], ['0'])).
% 0.84/1.02  thf('37', plain,
% 0.84/1.02      (![X32 : $i, X33 : $i]:
% 0.84/1.02         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 0.84/1.02      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.02  thf(t98_xboole_1, axiom,
% 0.84/1.02    (![A:$i,B:$i]:
% 0.84/1.02     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.84/1.02  thf('38', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((k2_xboole_0 @ X30 @ X31)
% 0.84/1.02           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.84/1.02  thf('39', plain,
% 0.84/1.02      (((r2_hidden @ sk_B @ sk_C)
% 0.84/1.02        | (r2_hidden @ sk_A @ sk_C)
% 0.84/1.02        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02            != (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('40', plain,
% 0.84/1.02      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf(t1_xboole_0, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.84/1.02       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.84/1.02  thf('41', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.84/1.02         ((r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.84/1.02          | (r2_hidden @ X0 @ X3)
% 0.84/1.02          | ~ (r2_hidden @ X0 @ X1))),
% 0.84/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.84/1.02  thf('42', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ((r2_hidden @ sk_A @ X0)
% 0.84/1.02           | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_C @ X0))))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.02  thf('43', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.84/1.02           | (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('sup+', [status(thm)], ['38', '42'])).
% 0.84/1.02  thf('44', plain,
% 0.84/1.02      (![X32 : $i, X33 : $i]:
% 0.84/1.02         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 0.84/1.02      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.02  thf('45', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.84/1.02      inference('sup+', [status(thm)], ['28', '29'])).
% 0.84/1.02  thf('46', plain,
% 0.84/1.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.84/1.02         ((r2_hidden @ X41 @ X42)
% 0.84/1.02          | ~ (r1_tarski @ (k2_tarski @ X41 @ X43) @ X42))),
% 0.84/1.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.84/1.02  thf('47', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (r2_hidden @ X1 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['45', '46'])).
% 0.84/1.02  thf('48', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((k2_xboole_0 @ X30 @ X31)
% 0.84/1.02           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.84/1.02  thf('49', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X0 @ X1)
% 0.84/1.02          | ~ (r2_hidden @ X0 @ X2)
% 0.84/1.02          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.84/1.02  thf('50', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.02          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.84/1.02          | ~ (r2_hidden @ X2 @ X1))),
% 0.84/1.02      inference('sup-', [status(thm)], ['48', '49'])).
% 0.84/1.02  thf('51', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X1 @ X2)
% 0.84/1.02          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['47', '50'])).
% 0.84/1.02  thf('52', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))
% 0.84/1.02          | ~ (r2_hidden @ X0 @ X2))),
% 0.84/1.02      inference('sup-', [status(thm)], ['44', '51'])).
% 0.84/1.02  thf('53', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C @ (k2_tarski @ X0 @ sk_A)))
% 0.84/1.02           | ~ (r2_hidden @ sk_A @ sk_C)))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['43', '52'])).
% 0.84/1.02  thf('54', plain,
% 0.84/1.02      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('55', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C @ (k2_tarski @ X0 @ sk_A))))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('demod', [status(thm)], ['53', '54'])).
% 0.84/1.02  thf('56', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.02          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.84/1.02          | ~ (r2_hidden @ X2 @ X1))),
% 0.84/1.02      inference('sup-', [status(thm)], ['48', '49'])).
% 0.84/1.02  thf('57', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          (~ (r2_hidden @ sk_A @ sk_C)
% 0.84/1.02           | ~ (r2_hidden @ sk_A @ 
% 0.84/1.02                (k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_C))))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['55', '56'])).
% 0.84/1.02  thf('58', plain,
% 0.84/1.02      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('59', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_C)))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('demod', [status(thm)], ['57', '58'])).
% 0.84/1.02  thf('60', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C)))
% 0.84/1.02         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['37', '59'])).
% 0.84/1.02  thf('61', plain,
% 0.84/1.02      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B)))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))) & 
% 0.84/1.02             ((r2_hidden @ sk_A @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['36', '60'])).
% 0.84/1.02  thf('62', plain,
% 0.84/1.02      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.84/1.02       ~
% 0.84/1.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['35', '61'])).
% 0.84/1.02  thf('63', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.84/1.02      inference('sat_resolution*', [status(thm)], ['2', '62'])).
% 0.84/1.02  thf('64', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.84/1.02      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 0.84/1.02  thf(t57_zfmisc_1, axiom,
% 0.84/1.02    (![A:$i,B:$i,C:$i]:
% 0.84/1.02     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.84/1.02          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.84/1.02  thf('65', plain,
% 0.84/1.02      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.84/1.02         ((r2_hidden @ X45 @ X46)
% 0.84/1.02          | (r1_xboole_0 @ (k2_tarski @ X45 @ X47) @ X46)
% 0.84/1.02          | (r2_hidden @ X47 @ X46))),
% 0.84/1.02      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.84/1.02  thf('66', plain,
% 0.84/1.02      (![X18 : $i, X19 : $i]:
% 0.84/1.02         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.84/1.02      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.84/1.02  thf('67', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         ((r2_hidden @ X1 @ X0)
% 0.84/1.02          | (r2_hidden @ X2 @ X0)
% 0.84/1.02          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.02  thf('68', plain,
% 0.84/1.02      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          != (k2_tarski @ sk_A @ sk_B)))
% 0.84/1.02         <= (~
% 0.84/1.02             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('69', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.84/1.02      inference('sup+', [status(thm)], ['23', '32'])).
% 0.84/1.02  thf('70', plain,
% 0.84/1.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.84/1.02         ((r2_hidden @ X43 @ X42)
% 0.84/1.02          | ~ (r1_tarski @ (k2_tarski @ X41 @ X43) @ X42))),
% 0.84/1.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.84/1.02  thf('71', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.84/1.02      inference('sup-', [status(thm)], ['69', '70'])).
% 0.84/1.02  thf('72', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((k2_xboole_0 @ X30 @ X31)
% 0.84/1.02           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.84/1.02  thf('73', plain,
% 0.84/1.02      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('74', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.84/1.02         ((r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.84/1.02          | (r2_hidden @ X0 @ X3)
% 0.84/1.02          | ~ (r2_hidden @ X0 @ X1))),
% 0.84/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.84/1.02  thf('75', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ((r2_hidden @ sk_B @ X0)
% 0.84/1.02           | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_C @ X0))))
% 0.84/1.02         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['73', '74'])).
% 0.84/1.02  thf('76', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ((r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ X0))
% 0.84/1.02           | (r2_hidden @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))
% 0.84/1.02         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('sup+', [status(thm)], ['72', '75'])).
% 0.84/1.02  thf('77', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))
% 0.84/1.02          | ~ (r2_hidden @ X0 @ X2))),
% 0.84/1.02      inference('sup-', [status(thm)], ['44', '51'])).
% 0.84/1.02  thf('78', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          ((r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k2_tarski @ X0 @ sk_B)))
% 0.84/1.02           | ~ (r2_hidden @ sk_B @ sk_C)))
% 0.84/1.02         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['76', '77'])).
% 0.84/1.02  thf('79', plain,
% 0.84/1.02      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('80', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k2_tarski @ X0 @ sk_B))))
% 0.84/1.02         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('demod', [status(thm)], ['78', '79'])).
% 0.84/1.02  thf('81', plain,
% 0.84/1.02      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))))),
% 0.84/1.02      inference('split', [status(esa)], ['0'])).
% 0.84/1.02  thf('82', plain,
% 0.84/1.02      (![X30 : $i, X31 : $i]:
% 0.84/1.02         ((k2_xboole_0 @ X30 @ X31)
% 0.84/1.02           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.84/1.02  thf('83', plain,
% 0.84/1.02      ((((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.84/1.02          = (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))))),
% 0.84/1.02      inference('sup+', [status(thm)], ['81', '82'])).
% 0.84/1.02  thf('84', plain,
% 0.84/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.02         (~ (r2_hidden @ X0 @ X1)
% 0.84/1.02          | ~ (r2_hidden @ X0 @ X2)
% 0.84/1.02          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.84/1.02      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.84/1.02  thf('85', plain,
% 0.84/1.02      ((![X0 : $i]:
% 0.84/1.02          (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 0.84/1.02           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.84/1.02           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))))),
% 0.84/1.02      inference('sup-', [status(thm)], ['83', '84'])).
% 0.84/1.02  thf('86', plain,
% 0.84/1.02      (((~ (r2_hidden @ sk_B @ sk_C)
% 0.84/1.02         | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B))))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))) & 
% 0.84/1.02             ((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['80', '85'])).
% 0.84/1.02  thf('87', plain,
% 0.84/1.02      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('88', plain,
% 0.84/1.02      ((~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))
% 0.84/1.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02                = (k2_tarski @ sk_A @ sk_B))) & 
% 0.84/1.02             ((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('demod', [status(thm)], ['86', '87'])).
% 0.84/1.02  thf('89', plain,
% 0.84/1.02      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 0.84/1.02       ~
% 0.84/1.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('sup-', [status(thm)], ['71', '88'])).
% 0.84/1.02  thf('90', plain,
% 0.84/1.02      (~
% 0.84/1.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B))) | 
% 0.84/1.02       ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 0.84/1.02      inference('split', [status(esa)], ['39'])).
% 0.84/1.02  thf('91', plain,
% 0.84/1.02      (~
% 0.84/1.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('sat_resolution*', [status(thm)], ['2', '62', '89', '90'])).
% 0.84/1.02  thf('92', plain,
% 0.84/1.02      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02         != (k2_tarski @ sk_A @ sk_B))),
% 0.84/1.02      inference('simpl_trail', [status(thm)], ['68', '91'])).
% 0.84/1.02  thf('93', plain,
% 0.84/1.02      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.84/1.02        | (r2_hidden @ sk_A @ sk_C)
% 0.84/1.02        | (r2_hidden @ sk_B @ sk_C))),
% 0.84/1.02      inference('sup-', [status(thm)], ['67', '92'])).
% 0.84/1.02  thf('94', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 0.84/1.02      inference('simplify', [status(thm)], ['93'])).
% 0.84/1.02  thf('95', plain,
% 0.84/1.02      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.84/1.02        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02            = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.02  thf('96', plain,
% 0.84/1.02      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.84/1.02      inference('split', [status(esa)], ['95'])).
% 0.84/1.02  thf('97', plain,
% 0.84/1.02      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 0.84/1.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.84/1.02          = (k2_tarski @ sk_A @ sk_B)))),
% 0.84/1.02      inference('split', [status(esa)], ['95'])).
% 0.84/1.02  thf('98', plain, (~ ((r2_hidden @ sk_B @ sk_C))),
% 0.84/1.02      inference('sat_resolution*', [status(thm)], ['2', '62', '89', '90', '97'])).
% 0.84/1.02  thf('99', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.84/1.02      inference('simpl_trail', [status(thm)], ['96', '98'])).
% 0.84/1.02  thf('100', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.84/1.02      inference('clc', [status(thm)], ['94', '99'])).
% 0.84/1.02  thf('101', plain, ($false), inference('demod', [status(thm)], ['64', '100'])).
% 0.84/1.02  
% 0.84/1.02  % SZS output end Refutation
% 0.84/1.02  
% 0.84/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
