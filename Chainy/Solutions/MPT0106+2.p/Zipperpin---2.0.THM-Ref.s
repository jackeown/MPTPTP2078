%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0106+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BbwrHBIV2l

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  161 ( 172 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t99_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) @ ( k4_xboole_0 @ ( B @ ( k2_xboole_0 @ ( A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( A @ B ) @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) @ ( k4_xboole_0 @ ( B @ ( k2_xboole_0 @ ( A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t99_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) @ ( k4_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
      = ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X191: $i,X192: $i,X193: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X191 @ X192 ) @ X193 ) )
      = ( k4_xboole_0 @ ( X191 @ ( k2_xboole_0 @ ( X192 @ X193 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('2',plain,(
    ! [X191: $i,X192: $i,X193: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X191 @ X192 ) @ X193 ) )
      = ( k4_xboole_0 @ ( X191 @ ( k2_xboole_0 @ ( X192 @ X193 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ C ) @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X194: $i,X195: $i,X196: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X194 @ X196 ) @ X195 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X194 @ X195 ) @ ( k4_xboole_0 @ ( X196 @ X195 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('6',plain,(
    ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) )
 != ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
