%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0526+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ow21FGErFU

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 6.24s
% Output     : Refutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   81 (  97 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B @ A ) )
       => ( ( k8_relat_1 @ ( A @ B ) )
          = B ) ) ) )).

thf('2',plain,(
    ! [X2198: $i,X2199: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2198 @ X2199 ) )
      | ( ( k8_relat_1 @ ( X2199 @ X2198 ) )
        = X2198 )
      | ~ ( v1_relat_1 @ X2198 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t126_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k8_relat_1 @ ( k2_relat_1 @ A @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t126_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ ( k2_relat_1 @ sk_A_5 @ sk_A_5 ) )
 != sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A_5 != sk_A_5 )
    | ~ ( v1_relat_1 @ sk_A_5 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_A_5 != sk_A_5 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
