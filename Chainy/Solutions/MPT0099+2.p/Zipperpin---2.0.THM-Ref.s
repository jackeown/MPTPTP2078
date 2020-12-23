%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0099+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xgUDnglIvE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  158 ( 212 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t92_xboole_1,conjecture,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k5_xboole_0 @ ( A @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t92_xboole_1])).

thf('0',plain,(
    ( k5_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ( k5_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( X0 @ X0 ) )
      = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('13',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ k1_xboole_0 ) )
      = X122 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ o_0_0_xboole_0 ) )
      = X122 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf('18',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['2','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
