%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0645+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cWmJr1pCHT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    3
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t52_funct_1,conjecture,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( v2_funct_1 @ ( k6_relat_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t52_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A_7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2648: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2648 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('2',plain,(
    $false ),
    inference(demod,[status(thm)],['0','1'])).

%------------------------------------------------------------------------------
