%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0272+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uVClLYWOAT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  119 ( 148 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ ( A @ B ) ) ) )).

thf('0',plain,(
    ! [X1011: $i,X1013: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1011 @ X1013 ) )
        = ( k1_tarski @ X1011 ) )
      | ( r2_hidden @ ( X1011 @ X1013 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('1',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k1_tarski @ sk_A_2 )
     != ( k1_tarski @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X1014: $i,X1016: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1016 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( X1014 @ X1016 ) ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X1014: $i,X1016: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1016 ) )
        = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( X1014 @ X1016 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','10'])).

%------------------------------------------------------------------------------
