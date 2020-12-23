%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0220+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y23Xuf8ym6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  176 ( 194 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) )
        = ( k2_tarski @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('2',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( B @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X704: $i,X705: $i,X706: $i] :
      ( ( k1_enumset1 @ ( X704 @ ( X705 @ X706 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X704 @ ( k2_tarski @ ( X705 @ X706 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( B @ ( C @ A ) ) ) ) )).

thf('5',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('6',plain,(
    ( k1_enumset1 @ ( sk_B_2 @ ( sk_A_2 @ sk_A_2 ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X870: $i] :
      ( ( k2_tarski @ ( X870 @ X870 ) )
      = ( k1_tarski @ X870 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X702: $i,X703: $i] :
      ( ( k2_tarski @ ( X702 @ X703 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X702 @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ ( X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 @ ( k2_tarski @ ( X0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X704: $i,X705: $i,X706: $i] :
      ( ( k1_enumset1 @ ( X704 @ ( X705 @ X706 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X704 @ ( k2_tarski @ ( X705 @ X706 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ ( X1 @ X0 ) )
      = ( k1_enumset1 @ ( X1 @ ( X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
