%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0122+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H4LZoKOHun

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   31 (  34 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t115_xboole_1,conjecture,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( r2_xboole_0 @ ( A @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t115_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ ( sk_A_2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    r2_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t62_xboole_1,axiom,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X302: $i] :
      ~ ( r2_xboole_0 @ ( X302 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X302: $i] :
      ~ ( r2_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    $false ),
    inference('sup-',[status(thm)],['2','5'])).

%------------------------------------------------------------------------------
