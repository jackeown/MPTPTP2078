%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0224+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6b2vT0nuRt

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:32 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :  115 ( 115 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X5 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X2: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X5 @ X2 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X8 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).


%------------------------------------------------------------------------------
