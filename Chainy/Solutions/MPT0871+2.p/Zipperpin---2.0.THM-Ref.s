%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0871+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cf1usSHoZQ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 6.15s
% Output     : Refutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  107 ( 107 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_D_93_type,type,(
    sk_D_93: $i )).

thf(sk_B_75_type,type,(
    sk_B_75: $i )).

thf(t31_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_mcart_1 @ ( A @ ( B @ ( C @ D ) ) ) )
        = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_mcart_1])).

thf('0',plain,(
    ( k4_mcart_1 @ ( sk_A_14 @ ( sk_B_75 @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ ( sk_A_14 @ sk_B_75 ) @ sk_C_93 ) @ sk_D_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ ( A @ ( B @ C ) ) )
      = ( k4_tarski @ ( k4_tarski @ ( A @ B ) @ C ) ) ) )).

thf('1',plain,(
    ! [X3784: $i,X3785: $i,X3786: $i] :
      ( ( k3_mcart_1 @ ( X3784 @ ( X3785 @ X3786 ) ) )
      = ( k4_tarski @ ( k4_tarski @ ( X3784 @ X3785 ) @ X3786 ) ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('2',plain,(
    ( k4_mcart_1 @ ( sk_A_14 @ ( sk_B_75 @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != ( k4_tarski @ ( k3_mcart_1 @ ( sk_A_14 @ ( sk_B_75 @ sk_C_93 ) ) @ sk_D_93 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k4_tarski @ ( k3_mcart_1 @ ( A @ ( B @ C ) ) @ D ) ) ) )).

thf('3',plain,(
    ! [X3787: $i,X3788: $i,X3789: $i,X3790: $i] :
      ( ( k4_mcart_1 @ ( X3787 @ ( X3788 @ ( X3789 @ X3790 ) ) ) )
      = ( k4_tarski @ ( k3_mcart_1 @ ( X3787 @ ( X3788 @ X3789 ) ) @ X3790 ) ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('4',plain,(
    ( k4_mcart_1 @ ( sk_A_14 @ ( sk_B_75 @ ( sk_C_93 @ sk_D_93 ) ) ) )
 != ( k4_mcart_1 @ ( sk_A_14 @ ( sk_B_75 @ ( sk_C_93 @ sk_D_93 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
