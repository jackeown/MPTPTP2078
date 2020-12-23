%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0067+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XZA5xW3BKd

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 137 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t60_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r1_tarski @ ( A @ B ) )
          & ( r2_xboole_0 @ ( B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( X40 @ X41 ) )
      | ~ ( r2_xboole_0 @ ( X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( sk_B_2 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X100: $i,X101: $i] :
      ( ( ( k2_xboole_0 @ ( X101 @ X100 ) )
        = X100 )
      | ~ ( r1_tarski @ ( X101 @ X100 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X100: $i,X101: $i] :
      ( ( ( k2_xboole_0 @ ( X101 @ X100 ) )
        = X100 )
      | ~ ( r1_tarski @ ( X101 @ X100 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A_2 = sk_B_2 ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    r2_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['0','11'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ ( A @ A ) ) )).

thf('13',plain,(
    ! [X45: $i] :
      ~ ( r2_xboole_0 @ ( X45 @ X45 ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('14',plain,(
    $false ),
    inference('sup-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
