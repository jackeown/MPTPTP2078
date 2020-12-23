%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0547+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j1dygh2jTY

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :  125 ( 168 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t149_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ ( A @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ ( A @ k1_xboole_0 ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t149_relat_1])).

thf('0',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ ( A @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X2179: $i] :
      ( ( ( k7_relat_1 @ ( X2179 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2179 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X2179: $i] :
      ( ( ( k7_relat_1 @ ( X2179 @ o_0_0_xboole_0 ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X2179 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,
    ( ( k7_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ ( B @ A ) ) )
        = ( k9_relat_1 @ ( B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X2261: $i,X2262: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( X2261 @ X2262 ) ) )
        = ( k9_relat_1 @ ( X2261 @ X2262 ) ) )
      | ~ ( v1_relat_1 @ X2261 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('7',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
      = ( k9_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_A_5 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( o_0_0_xboole_0
    = ( k9_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','11','12'])).

thf('14',plain,(
    ( k9_relat_1 @ ( sk_A_5 @ k1_xboole_0 ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ( k9_relat_1 @ ( sk_A_5 @ o_0_0_xboole_0 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','17'])).

%------------------------------------------------------------------------------
