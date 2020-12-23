%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0267+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SYBsQmb5ME

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  381 ( 707 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['9','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X6 )
      | ( X8
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_A = sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','18','19','20','32'])).


%------------------------------------------------------------------------------
