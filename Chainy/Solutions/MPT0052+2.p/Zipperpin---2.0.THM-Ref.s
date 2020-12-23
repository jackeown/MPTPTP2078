%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0052+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qvRys1NmHl

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   39 (  65 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  201 ( 377 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t45_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( B
        = ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ( B
          = ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_xboole_1])).

thf('0',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('6',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('7',plain,(
    ! [X149: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X149 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X149: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X149 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X94: $i,X95: $i] :
      ( ( ( k2_xboole_0 @ ( X95 @ X94 ) )
        = X94 )
      | ~ ( r1_tarski @ ( X95 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('13',plain,(
    ! [X175: $i,X176: $i] :
      ( ( k2_xboole_0 @ ( X175 @ ( k4_xboole_0 @ ( X176 @ X175 ) ) ) )
      = ( k2_xboole_0 @ ( X175 @ X176 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X94: $i,X95: $i] :
      ( ( ( k2_xboole_0 @ ( X95 @ X94 ) )
        = X94 )
      | ~ ( r1_tarski @ ( X95 @ X94 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B_2
 != ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('21',plain,(
    sk_B_2
 != ( k2_xboole_0 @ ( sk_A_2 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','21'])).

%------------------------------------------------------------------------------
