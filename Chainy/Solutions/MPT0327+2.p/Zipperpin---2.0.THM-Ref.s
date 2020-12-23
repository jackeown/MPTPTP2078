%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0327+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BWVUhaK9xX

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   52 (  88 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  303 ( 560 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ ( A @ B ) )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X1012: $i,X1014: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1012 @ X1014 ) )
      | ~ ( r2_hidden @ ( X1012 @ X1014 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_4 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('8',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_4 ) )
    = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('11',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k5_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) )
    = ( k4_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['8','9','14'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('16',plain,(
    ! [X242: $i,X243: $i] :
      ( ( k2_xboole_0 @ ( X242 @ ( k4_xboole_0 @ ( X243 @ X242 ) ) ) )
      = ( k2_xboole_0 @ ( X242 @ X243 ) ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k5_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_4 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_4 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_4 ) )
    = sk_B_4 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) )
    = sk_B_4 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k5_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ) )
    = sk_B_4 ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('25',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) @ ( k1_tarski @ sk_A_2 ) ) )
 != sk_B_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k4_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ) )
 != sk_B_4 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) )
    = ( k4_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['8','9','14'])).

thf('29',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k5_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) ) ) )
 != sk_B_4 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

%------------------------------------------------------------------------------
