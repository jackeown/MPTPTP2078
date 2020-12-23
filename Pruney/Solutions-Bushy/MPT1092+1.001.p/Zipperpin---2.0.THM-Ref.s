%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1092+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AU02XScC0X

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  101 ( 161 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t26_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
       => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
         => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_finset_1])).

thf('0',plain,(
    ~ ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(fc13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ X1 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_finset_1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_finset_1 @ ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).


%------------------------------------------------------------------------------
