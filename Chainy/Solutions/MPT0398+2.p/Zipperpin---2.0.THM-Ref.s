%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0398+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RWqSJYo2Jd

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   46 (  49 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(t20_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ ( k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ ( k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t20_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ ( k1_xboole_0 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ~ ( r1_setfam_1 @ ( o_0_0_xboole_0 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('3',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t17_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_setfam_1 @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X1836: $i,X1837: $i] :
      ( ( r1_setfam_1 @ ( X1836 @ X1837 ) )
      | ~ ( r1_tarski @ ( X1836 @ X1837 ) ) ) ),
    inference(cnf,[status(esa)],[t17_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ ( o_0_0_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['2','7'])).

%------------------------------------------------------------------------------
