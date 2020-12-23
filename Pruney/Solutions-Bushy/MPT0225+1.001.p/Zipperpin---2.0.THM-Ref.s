%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0225+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H6kU5OXtfZ

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  82 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  323 ( 830 expanded)
%              Number of equality atoms :   53 ( 142 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X5 ) @ X7 )
        = ( k1_tarski @ X5 ) )
      | ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('1',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('13',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('19',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['6','17'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).


%------------------------------------------------------------------------------
