%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0491+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.axLPyIejUM

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Timeout 58.21s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  122 ( 140 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ ( B @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X2246: $i,X2247: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( X2246 @ X2247 ) @ X2246 ) )
      | ~ ( v1_relat_1 @ X2246 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( A @ B ) )
           => ( ( r1_tarski @ ( k1_relat_1 @ A @ ( k1_relat_1 @ B ) ) )
              & ( r1_tarski @ ( k2_relat_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X2151: $i,X2152: $i] :
      ( ~ ( v1_relat_1 @ X2151 )
      | ( r1_tarski @ ( k1_relat_1 @ X2152 @ ( k1_relat_1 @ X2151 ) ) )
      | ~ ( r1_tarski @ ( X2152 @ X2151 ) )
      | ~ ( v1_relat_1 @ X2152 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( X0 @ X1 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ ( A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X2099: $i,X2100: $i] :
      ( ~ ( v1_relat_1 @ X2099 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( X2099 @ X2100 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(t89_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( B @ A ) ) @ ( k1_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( B @ A ) ) @ ( k1_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t89_relat_1])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) ) @ ( k1_relat_1 @ sk_B_15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v1_relat_1 @ sk_B_15 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['7','8'])).

%------------------------------------------------------------------------------
