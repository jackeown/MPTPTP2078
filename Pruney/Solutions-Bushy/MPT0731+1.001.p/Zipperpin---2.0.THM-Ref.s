%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0731+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUTTTN7oOy

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  19 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  62 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t14_ordinal1,conjecture,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( A
       != ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t14_ordinal1])).

thf('0',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['0','1'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['0','1'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['4','5'])).


%------------------------------------------------------------------------------
