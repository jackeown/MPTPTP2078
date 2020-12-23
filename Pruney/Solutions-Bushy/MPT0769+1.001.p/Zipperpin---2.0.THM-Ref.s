%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0769+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mtcwxKKUIU

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 164 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_wellord1 @ X4 @ X3 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) @ X2 )
        = ( k8_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf(t18_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ B @ A )
          = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_wellord1])).

thf('2',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_wellord1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_wellord1 @ sk_B @ sk_A )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).


%------------------------------------------------------------------------------
