%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0537+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8dQ2exDlUP

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   28 (  36 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 134 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(fc18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k8_relat_1 @ ( B @ A ) ) )
        & ( v1_relat_1 @ ( k8_relat_1 @ ( B @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X2121: $i,X2122: $i] :
      ( ~ ( v1_relat_1 @ X2121 )
      | ~ ( v1_xboole_0 @ X2122 )
      | ( v1_xboole_0 @ ( k8_relat_1 @ ( X2122 @ X2121 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc18_relat_1])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t137_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k1_xboole_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k8_relat_1 @ ( k1_xboole_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t137_relat_1])).

thf('2',plain,(
    ( k8_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ( k8_relat_1 @ ( o_0_0_xboole_0 @ sk_A_5 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k8_relat_1 @ ( o_0_0_xboole_0 @ sk_A_5 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k8_relat_1 @ ( o_0_0_xboole_0 @ sk_A_5 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ ( k8_relat_1 @ ( o_0_0_xboole_0 @ sk_A_5 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['7','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A_5 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('14',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['12','13','14'])).

%------------------------------------------------------------------------------
