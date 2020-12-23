%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0790+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y9XgrZGOV3

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   22 (  26 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  135 ( 191 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t13_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_wellord1 @ B @ A ) @ ( k3_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t13_wellord1])).

thf(t39_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( v2_wellord1 @ B )
          & ( r1_tarski @ A @ ( k3_relat_1 @ B ) ) )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) )
          = A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v2_wellord1 @ X2 )
      | ~ ( r1_tarski @ X3 @ ( k3_relat_1 @ X2 ) )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X2 @ X3 ) )
        = X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t39_wellord1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) )
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( ( k3_relat_1 @ ( k2_wellord1 @ X0 @ ( k1_wellord1 @ X0 @ X1 ) ) )
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t40_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
          = ( k1_wellord1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( v2_wellord1 @ B )
         => ( ( k3_relat_1 @ ( k2_wellord1 @ B @ ( k1_wellord1 @ B @ A ) ) )
            = ( k1_wellord1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_wellord1])).

thf('4',plain,(
    ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ ( k1_wellord1 @ sk_B @ sk_A ) ) )
 != ( k1_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_wellord1 @ sk_B @ sk_A )
     != ( k1_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v2_wellord1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_wellord1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ( k1_wellord1 @ sk_B @ sk_A )
 != ( k1_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).


%------------------------------------------------------------------------------
