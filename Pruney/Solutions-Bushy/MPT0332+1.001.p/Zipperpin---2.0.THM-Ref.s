%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0332+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kzfArW0n3

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 189 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['0','8'])).


%------------------------------------------------------------------------------
