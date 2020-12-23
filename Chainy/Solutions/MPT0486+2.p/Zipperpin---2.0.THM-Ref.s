%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0486+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.crMmCMEzbC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 114 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X2206: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2206 ) )
      = X2206 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X2202: $i] :
      ( ( ( k1_relat_1 @ X2202 )
       != k1_xboole_0 )
      | ( X2202 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2202 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X2202: $i] :
      ( ( ( k1_relat_1 @ X2202 )
       != o_0_0_xboole_0 )
      | ( X2202 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X2202 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X2092: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2092 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k6_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['7'])).

thf(t81_relat_1,conjecture,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k6_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t81_relat_1])).

thf('9',plain,(
    ( k6_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ( k6_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','12'])).

%------------------------------------------------------------------------------
