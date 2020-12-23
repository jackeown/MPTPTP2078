%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0124+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jpMHz0yTnN

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 5.32s
% Output     : Refutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   59 (  74 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  394 ( 513 expanded)
%              Number of equality atoms :   46 (  61 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t117_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( C @ B ) )
     => ( ( k4_xboole_0 @ ( A @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( C @ B ) )
       => ( ( k4_xboole_0 @ ( A @ C ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( sk_C_5 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,
    ( ( k5_xboole_0 @ ( sk_C_5 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('9',plain,(
    ! [X180: $i] :
      ( ( k2_xboole_0 @ ( X180 @ k1_xboole_0 ) )
      = X180 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X180: $i] :
      ( ( k2_xboole_0 @ ( X180 @ o_0_0_xboole_0 ) )
      = X180 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k5_xboole_0 @ ( sk_C_5 @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('15',plain,(
    ! [X277: $i,X278: $i,X279: $i] :
      ( ( k4_xboole_0 @ ( X277 @ ( k4_xboole_0 @ ( X278 @ X279 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X277 @ X278 ) @ ( k3_xboole_0 @ ( X277 @ X279 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X44: $i] :
      ( ( k3_xboole_0 @ ( X44 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t102_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ( k4_xboole_0 @ ( X108 @ ( k5_xboole_0 @ ( X109 @ X110 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X108 @ ( k2_xboole_0 @ ( X109 @ X110 ) ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X110 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t102_xboole_1])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ( k4_xboole_0 @ ( X108 @ ( k5_xboole_0 @ ( X109 @ X110 ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( X108 @ X109 ) @ X110 ) @ ( k4_xboole_0 @ ( X108 @ ( k2_xboole_0 @ ( X109 @ X110 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k5_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ ( k4_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X259: $i,X260: $i] :
      ( ( k4_xboole_0 @ ( X259 @ ( k2_xboole_0 @ ( X259 @ X260 ) ) ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    ! [X259: $i,X260: $i] :
      ( ( k4_xboole_0 @ ( X259 @ ( k2_xboole_0 @ ( X259 @ X260 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k5_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k3_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( X0 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    r1_tarski @ ( sk_C_5 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('31',plain,(
    ! [X207: $i,X208: $i] :
      ( ( ( k3_xboole_0 @ ( X207 @ X208 ) )
        = X207 )
      | ~ ( r1_tarski @ ( X207 @ X208 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_B_2 ) )
    = sk_C_5 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
 != ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(demod,[status(thm)],['14','15','28','29','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
