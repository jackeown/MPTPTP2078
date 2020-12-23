%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UD33KFhj8T

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:02 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  122 (4274 expanded)
%              Number of leaves         :   18 (1123 expanded)
%              Depth                    :   30
%              Number of atoms          : 1010 (44335 expanded)
%              Number of equality atoms :  179 (8650 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X8 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('11',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X21: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X19 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ sk_A @ X0 ) )
         != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( sk_A != sk_A )
        | ( ( sk_B @ ( k2_tarski @ sk_A @ X0 ) )
          = X0 )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 )
        | ( ( sk_B @ ( k2_tarski @ sk_A @ X0 ) )
          = X0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('28',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( X0
         != ( k4_tarski @ X2 @ X1 ) )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 )
        | ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ X0 ) )
        | ( ( k2_tarski @ sk_A @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X1: $i,X2: $i] :
        ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ sk_A @ ( k4_tarski @ X2 @ X1 ) ) )
        | ( ( k2_tarski @ sk_A @ ( k4_tarski @ X2 @ X1 ) )
          = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k2_tarski @ sk_A @ ( k4_tarski @ X0 @ sk_A ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ ( k4_tarski @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','44','45'])).

thf('47',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( k4_tarski @ X0 @ sk_A )
        = sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( k1_mcart_1 @ sk_A )
        = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['0','1'])).

thf('53',plain,
    ( ! [X0: $i] : ( sk_B_1 = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] : ( sk_B_1 = X0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('57',plain,
    ( ! [X0: $i] : ( X0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('60',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['7','60'])).

thf('62',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('64',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X3 ) )
        = X3 )
      | ( ( k2_tarski @ X0 @ X3 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X3 ) )
      | ( ( k2_tarski @ X0 @ X3 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) )
      | ( ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) )
        = X3 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ X0 ) )
        = X0 )
      | ( ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( k2_tarski @ ( k4_tarski @ X3 @ X0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k2_tarski @ ( k4_tarski @ X3 @ X0 ) @ X0 ) )
      | ( ( k2_tarski @ ( k4_tarski @ X3 @ X0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ ( k4_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) ) @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k2_tarski @ ( k4_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) ) @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ ( k4_tarski @ X0 @ ( k4_tarski @ sk_A @ sk_C_1 ) ) @ sk_A ) )
      | ( ( k2_tarski @ ( k4_tarski @ X0 @ ( k4_tarski @ sk_A @ sk_C_1 ) ) @ ( k4_tarski @ sk_A @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['7','60'])).

thf('73',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('74',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['7','60'])).

thf('75',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['7','60'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ ( k4_tarski @ X0 @ sk_A ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('80',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_tarski @ X0 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ sk_A )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('94',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('95',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('98',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('99',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] : ( X0 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    $false ),
    inference(simplify,[status(thm)],['101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UD33KFhj8T
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.44  % Solved by: fo/fo7.sh
% 1.20/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.44  % done 1178 iterations in 0.993s
% 1.20/1.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.44  % SZS output start Refutation
% 1.20/1.44  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.20/1.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.20/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.44  thf(sk_B_type, type, sk_B: $i > $i).
% 1.20/1.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.20/1.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.20/1.44  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.20/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.20/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.20/1.44  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.20/1.44  thf(t20_mcart_1, conjecture,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 1.20/1.44       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 1.20/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.44    (~( ![A:$i]:
% 1.20/1.44        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 1.20/1.44          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 1.20/1.44    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 1.20/1.44  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(t7_mcart_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 1.20/1.44       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 1.20/1.44  thf('1', plain,
% 1.20/1.44      (![X19 : $i, X20 : $i]: ((k1_mcart_1 @ (k4_tarski @ X19 @ X20)) = (X19))),
% 1.20/1.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.20/1.44  thf('2', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 1.20/1.44      inference('sup+', [status(thm)], ['0', '1'])).
% 1.20/1.44  thf('3', plain,
% 1.20/1.44      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('4', plain,
% 1.20/1.44      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('split', [status(esa)], ['3'])).
% 1.20/1.44  thf('5', plain,
% 1.20/1.44      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['2', '4'])).
% 1.20/1.44  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('7', plain,
% 1.20/1.44      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 1.20/1.44         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['5', '6'])).
% 1.20/1.44  thf(d2_tarski, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.20/1.44       ( ![D:$i]:
% 1.20/1.44         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.20/1.44  thf('8', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.20/1.44         (((X6) != (X8))
% 1.20/1.44          | (r2_hidden @ X6 @ X7)
% 1.20/1.44          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 1.20/1.44      inference('cnf', [status(esa)], [d2_tarski])).
% 1.20/1.44  thf('9', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X8 @ X5))),
% 1.20/1.44      inference('simplify', [status(thm)], ['8'])).
% 1.20/1.44  thf(t9_mcart_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.20/1.44          ( ![B:$i]:
% 1.20/1.44            ( ~( ( r2_hidden @ B @ A ) & 
% 1.20/1.44                 ( ![C:$i,D:$i]:
% 1.20/1.44                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.20/1.44                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.20/1.44  thf('10', plain,
% 1.20/1.44      (![X22 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('11', plain,
% 1.20/1.44      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.44         (~ (r2_hidden @ X9 @ X7)
% 1.20/1.44          | ((X9) = (X8))
% 1.20/1.44          | ((X9) = (X5))
% 1.20/1.44          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 1.20/1.44      inference('cnf', [status(esa)], [d2_tarski])).
% 1.20/1.44  thf('12', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i, X9 : $i]:
% 1.20/1.44         (((X9) = (X5))
% 1.20/1.44          | ((X9) = (X8))
% 1.20/1.44          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['11'])).
% 1.20/1.44  thf('13', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 1.20/1.44          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 1.20/1.44          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['10', '12'])).
% 1.20/1.44  thf('14', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X8 @ X5))),
% 1.20/1.44      inference('simplify', [status(thm)], ['8'])).
% 1.20/1.44  thf('15', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('16', plain,
% 1.20/1.44      (![X19 : $i, X21 : $i]: ((k2_mcart_1 @ (k4_tarski @ X19 @ X21)) = (X21))),
% 1.20/1.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.20/1.44  thf('17', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 1.20/1.44      inference('sup+', [status(thm)], ['15', '16'])).
% 1.20/1.44  thf('18', plain,
% 1.20/1.44      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('split', [status(esa)], ['3'])).
% 1.20/1.44  thf('19', plain,
% 1.20/1.44      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['17', '18'])).
% 1.20/1.44  thf('20', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('21', plain,
% 1.20/1.44      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['19', '20'])).
% 1.20/1.44  thf('22', plain,
% 1.20/1.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X23 @ X22)
% 1.20/1.44          | ((sk_B @ X22) != (k4_tarski @ X24 @ X23)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('23', plain,
% 1.20/1.44      ((![X0 : $i]:
% 1.20/1.44          (((sk_B @ X0) != (sk_A))
% 1.20/1.44           | ~ (r2_hidden @ sk_A @ X0)
% 1.20/1.44           | ((X0) = (k1_xboole_0))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['21', '22'])).
% 1.20/1.44  thf('24', plain,
% 1.20/1.44      ((![X0 : $i]:
% 1.20/1.44          (((k2_tarski @ sk_A @ X0) = (k1_xboole_0))
% 1.20/1.44           | ((sk_B @ (k2_tarski @ sk_A @ X0)) != (sk_A))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['14', '23'])).
% 1.20/1.44  thf('25', plain,
% 1.20/1.44      ((![X0 : $i]:
% 1.20/1.44          (((sk_A) != (sk_A))
% 1.20/1.44           | ((sk_B @ (k2_tarski @ sk_A @ X0)) = (X0))
% 1.20/1.44           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))
% 1.20/1.44           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['13', '24'])).
% 1.20/1.44  thf('26', plain,
% 1.20/1.44      ((![X0 : $i]:
% 1.20/1.44          (((k2_tarski @ sk_A @ X0) = (k1_xboole_0))
% 1.20/1.44           | ((sk_B @ (k2_tarski @ sk_A @ X0)) = (X0))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('simplify', [status(thm)], ['25'])).
% 1.20/1.44  thf('27', plain,
% 1.20/1.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X23 @ X22)
% 1.20/1.44          | ((sk_B @ X22) != (k4_tarski @ X24 @ X23)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('28', plain,
% 1.20/1.44      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44          (((X0) != (k4_tarski @ X2 @ X1))
% 1.20/1.44           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))
% 1.20/1.44           | ~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ X0))
% 1.20/1.44           | ((k2_tarski @ sk_A @ X0) = (k1_xboole_0))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['26', '27'])).
% 1.20/1.44  thf('29', plain,
% 1.20/1.44      ((![X1 : $i, X2 : $i]:
% 1.20/1.44          (~ (r2_hidden @ X1 @ (k2_tarski @ sk_A @ (k4_tarski @ X2 @ X1)))
% 1.20/1.44           | ((k2_tarski @ sk_A @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('simplify', [status(thm)], ['28'])).
% 1.20/1.44  thf('30', plain,
% 1.20/1.44      ((![X0 : $i]:
% 1.20/1.44          ((k2_tarski @ sk_A @ (k4_tarski @ X0 @ sk_A)) = (k1_xboole_0)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['9', '29'])).
% 1.20/1.44  thf('31', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.20/1.44         (((X6) != (X5))
% 1.20/1.44          | (r2_hidden @ X6 @ X7)
% 1.20/1.44          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 1.20/1.44      inference('cnf', [status(esa)], [d2_tarski])).
% 1.20/1.44  thf('32', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 1.20/1.44      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.44  thf('33', plain,
% 1.20/1.44      ((![X0 : $i]: (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ k1_xboole_0))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['30', '32'])).
% 1.20/1.44  thf('34', plain,
% 1.20/1.44      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['19', '20'])).
% 1.20/1.44  thf('35', plain,
% 1.20/1.44      (![X22 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf(d1_tarski, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.20/1.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.20/1.44  thf('36', plain,
% 1.20/1.44      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.20/1.44         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 1.20/1.44      inference('cnf', [status(esa)], [d1_tarski])).
% 1.20/1.44  thf('37', plain,
% 1.20/1.44      (![X0 : $i, X3 : $i]:
% 1.20/1.44         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['36'])).
% 1.20/1.44  thf('38', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.20/1.44          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['35', '37'])).
% 1.20/1.44  thf('39', plain,
% 1.20/1.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X23 @ X22)
% 1.20/1.44          | ((sk_B @ X22) != (k4_tarski @ X24 @ X23)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('40', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44         (((X0) != (k4_tarski @ X2 @ X1))
% 1.20/1.44          | ((k1_tarski @ X0) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.20/1.44          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.20/1.44  thf('41', plain,
% 1.20/1.44      (![X1 : $i, X2 : $i]:
% 1.20/1.44         (~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 1.20/1.44          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['40'])).
% 1.20/1.44  thf('42', plain,
% 1.20/1.44      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 1.20/1.44         | ((k1_tarski @ (k4_tarski @ sk_B_1 @ sk_A)) = (k1_xboole_0))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['34', '41'])).
% 1.20/1.44  thf('43', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 1.20/1.44      inference('cnf', [status(esa)], [d1_tarski])).
% 1.20/1.44  thf('44', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.20/1.44      inference('simplify', [status(thm)], ['43'])).
% 1.20/1.44  thf('45', plain,
% 1.20/1.44      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['19', '20'])).
% 1.20/1.44  thf('46', plain,
% 1.20/1.44      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('demod', [status(thm)], ['42', '44', '45'])).
% 1.20/1.44  thf('47', plain,
% 1.20/1.44      (![X0 : $i, X3 : $i]:
% 1.20/1.44         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['36'])).
% 1.20/1.44  thf('48', plain,
% 1.20/1.44      ((![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A))))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['46', '47'])).
% 1.20/1.44  thf('49', plain,
% 1.20/1.44      ((![X0 : $i]: ((k4_tarski @ X0 @ sk_A) = (sk_A)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['33', '48'])).
% 1.20/1.44  thf('50', plain,
% 1.20/1.44      (![X19 : $i, X20 : $i]: ((k1_mcart_1 @ (k4_tarski @ X19 @ X20)) = (X19))),
% 1.20/1.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.20/1.44  thf('51', plain,
% 1.20/1.44      ((![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['49', '50'])).
% 1.20/1.44  thf('52', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 1.20/1.44      inference('sup+', [status(thm)], ['0', '1'])).
% 1.20/1.44  thf('53', plain,
% 1.20/1.44      ((![X0 : $i]: ((sk_B_1) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.44  thf('54', plain,
% 1.20/1.44      ((![X0 : $i]: ((sk_B_1) = (X0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.44  thf('55', plain,
% 1.20/1.44      ((![X0 : $i, X1 : $i]: ((X0) = (X1)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['53', '54'])).
% 1.20/1.44  thf(t49_zfmisc_1, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.20/1.44  thf('56', plain,
% 1.20/1.44      (![X17 : $i, X18 : $i]:
% 1.20/1.44         ((k2_xboole_0 @ (k1_tarski @ X17) @ X18) != (k1_xboole_0))),
% 1.20/1.44      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.20/1.44  thf('57', plain,
% 1.20/1.44      ((![X0 : $i]: ((X0) != (k1_xboole_0)))
% 1.20/1.44         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['55', '56'])).
% 1.20/1.44  thf('58', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['57'])).
% 1.20/1.44  thf('59', plain,
% 1.20/1.44      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 1.20/1.44      inference('split', [status(esa)], ['3'])).
% 1.20/1.44  thf('60', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.20/1.44      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 1.20/1.44  thf('61', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 1.20/1.44      inference('simpl_trail', [status(thm)], ['7', '60'])).
% 1.20/1.44  thf('62', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 1.20/1.44      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.44  thf('63', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 1.20/1.44          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 1.20/1.44          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['10', '12'])).
% 1.20/1.44  thf('64', plain,
% 1.20/1.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X23 @ X22)
% 1.20/1.44          | ((sk_B @ X22) != (k4_tarski @ X24 @ X23)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('65', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.44         (((X0) != (k4_tarski @ X2 @ X1))
% 1.20/1.44          | ((sk_B @ (k2_tarski @ X0 @ X3)) = (X3))
% 1.20/1.44          | ((k2_tarski @ X0 @ X3) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X3))
% 1.20/1.44          | ((k2_tarski @ X0 @ X3) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['63', '64'])).
% 1.20/1.44  thf('66', plain,
% 1.20/1.44      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.44         (~ (r2_hidden @ X1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X3))
% 1.20/1.44          | ((k2_tarski @ (k4_tarski @ X2 @ X1) @ X3) = (k1_xboole_0))
% 1.20/1.44          | ((sk_B @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X3)) = (X3)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['65'])).
% 1.20/1.44  thf('67', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         (((sk_B @ (k2_tarski @ (k4_tarski @ X1 @ X0) @ X0)) = (X0))
% 1.20/1.44          | ((k2_tarski @ (k4_tarski @ X1 @ X0) @ X0) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['62', '66'])).
% 1.20/1.44  thf('68', plain,
% 1.20/1.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X24 @ X22)
% 1.20/1.44          | ((sk_B @ X22) != (k4_tarski @ X24 @ X23)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('69', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.44         (((X0) != (k4_tarski @ X2 @ X1))
% 1.20/1.44          | ((k2_tarski @ (k4_tarski @ X3 @ X0) @ X0) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X2 @ (k2_tarski @ (k4_tarski @ X3 @ X0) @ X0))
% 1.20/1.44          | ((k2_tarski @ (k4_tarski @ X3 @ X0) @ X0) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['67', '68'])).
% 1.20/1.44  thf('70', plain,
% 1.20/1.44      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.44         (~ (r2_hidden @ X2 @ 
% 1.20/1.44             (k2_tarski @ (k4_tarski @ X3 @ (k4_tarski @ X2 @ X1)) @ 
% 1.20/1.44              (k4_tarski @ X2 @ X1)))
% 1.20/1.44          | ((k2_tarski @ (k4_tarski @ X3 @ (k4_tarski @ X2 @ X1)) @ 
% 1.20/1.44              (k4_tarski @ X2 @ X1)) = (k1_xboole_0)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['69'])).
% 1.20/1.44  thf('71', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (r2_hidden @ sk_A @ 
% 1.20/1.44             (k2_tarski @ (k4_tarski @ X0 @ (k4_tarski @ sk_A @ sk_C_1)) @ sk_A))
% 1.20/1.44          | ((k2_tarski @ (k4_tarski @ X0 @ (k4_tarski @ sk_A @ sk_C_1)) @ 
% 1.20/1.44              (k4_tarski @ sk_A @ sk_C_1)) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['61', '70'])).
% 1.20/1.44  thf('72', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 1.20/1.44      inference('simpl_trail', [status(thm)], ['7', '60'])).
% 1.20/1.44  thf('73', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 1.20/1.44      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.44  thf('74', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 1.20/1.44      inference('simpl_trail', [status(thm)], ['7', '60'])).
% 1.20/1.44  thf('75', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 1.20/1.44      inference('simpl_trail', [status(thm)], ['7', '60'])).
% 1.20/1.44  thf('76', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         ((k2_tarski @ (k4_tarski @ X0 @ sk_A) @ sk_A) = (k1_xboole_0))),
% 1.20/1.44      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 1.20/1.44  thf('77', plain,
% 1.20/1.44      (![X5 : $i, X8 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X8 @ X5))),
% 1.20/1.44      inference('simplify', [status(thm)], ['8'])).
% 1.20/1.44  thf('78', plain,
% 1.20/1.44      (![X0 : $i]: (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ k1_xboole_0)),
% 1.20/1.44      inference('sup+', [status(thm)], ['76', '77'])).
% 1.20/1.44  thf('79', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.20/1.44      inference('simplify', [status(thm)], ['43'])).
% 1.20/1.44  thf('80', plain,
% 1.20/1.44      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 1.20/1.44         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup+', [status(thm)], ['5', '6'])).
% 1.20/1.44  thf('81', plain,
% 1.20/1.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.44         (((X22) = (k1_xboole_0))
% 1.20/1.44          | ~ (r2_hidden @ X24 @ X22)
% 1.20/1.44          | ((sk_B @ X22) != (k4_tarski @ X24 @ X23)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.20/1.44  thf('82', plain,
% 1.20/1.44      ((![X0 : $i]:
% 1.20/1.44          (((sk_B @ X0) != (sk_A))
% 1.20/1.44           | ~ (r2_hidden @ sk_A @ X0)
% 1.20/1.44           | ((X0) = (k1_xboole_0))))
% 1.20/1.44         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['80', '81'])).
% 1.20/1.44  thf('83', plain,
% 1.20/1.44      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.20/1.44         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 1.20/1.44         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['79', '82'])).
% 1.20/1.44  thf('84', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.20/1.44          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['35', '37'])).
% 1.20/1.44  thf('85', plain,
% 1.20/1.44      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 1.20/1.44         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('clc', [status(thm)], ['83', '84'])).
% 1.20/1.44  thf('86', plain,
% 1.20/1.44      (![X0 : $i, X3 : $i]:
% 1.20/1.44         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['36'])).
% 1.20/1.44  thf('87', plain,
% 1.20/1.44      ((![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A))))
% 1.20/1.44         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['85', '86'])).
% 1.20/1.44  thf('88', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.20/1.44      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 1.20/1.44  thf('89', plain,
% 1.20/1.44      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A)))),
% 1.20/1.44      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 1.20/1.44  thf('90', plain, (![X0 : $i]: ((k4_tarski @ X0 @ sk_A) = (sk_A))),
% 1.20/1.44      inference('sup-', [status(thm)], ['78', '89'])).
% 1.20/1.44  thf('91', plain,
% 1.20/1.44      (![X19 : $i, X20 : $i]: ((k1_mcart_1 @ (k4_tarski @ X19 @ X20)) = (X19))),
% 1.20/1.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.20/1.44  thf('92', plain, (![X0 : $i]: ((k1_mcart_1 @ sk_A) = (X0))),
% 1.20/1.44      inference('sup+', [status(thm)], ['90', '91'])).
% 1.20/1.44  thf('93', plain,
% 1.20/1.44      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 1.20/1.44      inference('split', [status(esa)], ['3'])).
% 1.20/1.44  thf('94', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 1.20/1.44      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 1.20/1.44  thf('95', plain, (((sk_A) = (k1_mcart_1 @ sk_A))),
% 1.20/1.44      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 1.20/1.44  thf('96', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['92', '95'])).
% 1.20/1.44  thf('97', plain,
% 1.20/1.44      (![X17 : $i, X18 : $i]:
% 1.20/1.44         ((k2_xboole_0 @ (k1_tarski @ X17) @ X18) != (k1_xboole_0))),
% 1.20/1.44      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 1.20/1.44  thf('98', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['92', '95'])).
% 1.20/1.44  thf('99', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['92', '95'])).
% 1.20/1.44  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 1.20/1.44      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.20/1.44  thf('101', plain, (![X0 : $i]: ((X0) != (k1_xboole_0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['96', '100'])).
% 1.20/1.44  thf('102', plain, ($false), inference('simplify', [status(thm)], ['101'])).
% 1.20/1.44  
% 1.20/1.44  % SZS output end Refutation
% 1.20/1.44  
% 1.20/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
