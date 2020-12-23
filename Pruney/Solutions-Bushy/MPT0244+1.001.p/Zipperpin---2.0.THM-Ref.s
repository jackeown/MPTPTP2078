%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0244+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ipX5bidzQl

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 194 expanded)
%              Number of leaves         :    7 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  301 (1794 expanded)
%              Number of equality atoms :   47 ( 308 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('12',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_A != k1_xboole_0 )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['5','7','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_tarski @ X2 ) )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('19',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','7','16','23','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','17','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','7','16','23','24'])).

thf('29',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_tarski @ X2 ) )
      | ( X1
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,(
    ! [X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['27','28'])).

thf('34',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['26','34'])).


%------------------------------------------------------------------------------
