%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0227+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tnq5wFFAVA

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 5.42s
% Output     : Refutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  132 ( 135 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t22_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t22_zfmisc_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('3',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('5',plain,(
    ! [X441: $i,X442: $i,X443: $i,X444: $i] :
      ( ( X442 != X441 )
      | ( r2_hidden @ ( X442 @ X443 ) )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('6',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X441 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('7',plain,(
    ! [X990: $i,X992: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X990 @ X992 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( X990 @ X992 ) ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X990: $i,X992: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X990 @ X992 ) )
        = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( X990 @ X992 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 @ ( k2_tarski @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['4','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
