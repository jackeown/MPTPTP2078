%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XNEcVJv8bV

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  60 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 416 expanded)
%              Number of equality atoms :   20 (  53 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t37_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = k1_xboole_0 )
      <=> ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','9','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['11','18'])).


%------------------------------------------------------------------------------
