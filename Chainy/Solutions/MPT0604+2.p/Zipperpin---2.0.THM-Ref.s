%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0604+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dX76ciU6pk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   60 (  60 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_6_type,type,(
    sk_A_6: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t208_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( A @ A ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( A @ A ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t208_relat_1])).

thf('0',plain,(
    ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( sk_A_6 @ sk_A_6 ) ) ) )
 != ( k1_tarski @ sk_A_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( A @ B ) ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X2470: $i,X2471: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ ( X2470 @ X2471 ) ) ) )
      = ( k2_tarski @ ( X2470 @ X2471 ) ) ) ),
    inference(cnf,[status(esa)],[t32_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ( k1_tarski @ sk_A_6 )
 != ( k1_tarski @ sk_A_6 ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
