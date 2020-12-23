%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0328+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MCUq8FQz53

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 112 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t141_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ ( A @ B ) )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( r2_hidden @ ( A @ B ) )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t141_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_A_2 @ sk_B_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ ( k1_tarski @ B ) ) )
        = A )
    <=> ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X1331: $i,X1332: $i] :
      ( ( ( k4_xboole_0 @ ( X1331 @ ( k1_tarski @ X1332 ) ) )
        = X1331 )
      | ( r2_hidden @ ( X1332 @ X1331 ) ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('2',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) @ ( k1_tarski @ sk_A_2 ) ) )
 != sk_B_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X246: $i,X247: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X246 @ X247 ) @ X247 ) )
      = ( k4_xboole_0 @ ( X246 @ X247 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ( k4_xboole_0 @ ( sk_B_4 @ ( k1_tarski @ sk_A_2 ) ) )
 != sk_B_4 ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B_4 != sk_B_4 )
    | ( r2_hidden @ ( sk_A_2 @ sk_B_4 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_4 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    $false ),
    inference(demod,[status(thm)],['0','6'])).

%------------------------------------------------------------------------------
