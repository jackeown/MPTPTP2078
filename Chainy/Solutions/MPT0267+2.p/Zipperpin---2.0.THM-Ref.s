%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0267+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.89ELTiHrbB

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  403 ( 719 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ ( A @ ( k4_xboole_0 @ ( B @ ( k1_tarski @ C ) ) ) ) )
    <=> ( ( r2_hidden @ ( A @ B ) )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ ( A @ ( k4_xboole_0 @ ( B @ ( k1_tarski @ C ) ) ) ) )
      <=> ( ( r2_hidden @ ( A @ B ) )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('0',plain,
    ( ( sk_A_2 != sk_C_10 )
    | ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A_2 != sk_C_10 )
    | ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A_2 = sk_C_10 )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A_2 = sk_C_10 )
   <= ( sk_A_2 = sk_C_10 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_A_2 ) ) ) ) )
   <= ( ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
      & ( sk_A_2 = sk_C_10 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ~ ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( X33 @ X32 ) )
      | ~ ( r2_hidden @ ( X33 @ X31 ) )
      | ( X32
       != ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( X33 @ X31 ) )
      | ~ ( r2_hidden @ ( X33 @ ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ ( k1_tarski @ sk_A_2 ) ) )
   <= ( ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
      & ( sk_A_2 = sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('12',plain,(
    ! [X993: $i,X994: $i] :
      ( ( r2_hidden @ ( X993 @ X994 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X993 @ X994 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A_2 != sk_C_10 )
    | ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( X33 @ X32 ) )
      | ( r2_hidden @ ( X33 @ X30 ) )
      | ( X32
       != ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( X33 @ X30 ) )
      | ~ ( r2_hidden @ ( X33 @ ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
    | ( sk_A_2 = sk_C_10 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ ( X29 @ X30 ) )
      | ( r2_hidden @ ( X29 @ X31 ) )
      | ( r2_hidden @ ( X29 @ X32 ) )
      | ( X32
       != ( k4_xboole_0 @ ( X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( X29 @ ( k4_xboole_0 @ ( X30 @ X31 ) ) ) )
      | ( r2_hidden @ ( X29 @ X31 ) )
      | ~ ( r2_hidden @ ( X29 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_A_2 @ X0 ) )
        | ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_A_2 @ ( k1_tarski @ sk_C_10 ) ) )
   <= ( ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
      & ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A_2 = sk_C_10 )
   <= ( ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
      & ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_A_2 != sk_C_10 )
   <= ( sk_A_2 != sk_C_10 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( sk_A_2 != sk_A_2 )
   <= ( ( sk_A_2 != sk_C_10 )
      & ~ ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
      & ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ ( k1_tarski @ sk_C_10 ) ) ) ) )
    | ( sk_A_2 = sk_C_10 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','20','21','22','34'])).

%------------------------------------------------------------------------------
