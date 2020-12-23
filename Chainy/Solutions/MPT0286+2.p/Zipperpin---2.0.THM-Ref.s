%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0286+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lkqyeYU3u8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t93_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( A @ B ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( A @ B ) ) )
        = ( k2_xboole_0 @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) )
 != ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( A @ B ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X1032: $i,X1033: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( X1032 @ X1033 ) ) )
      = ( k2_xboole_0 @ ( X1032 @ X1033 ) ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
 != ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
