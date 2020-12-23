%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0279+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.945rHJTB7G

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t80_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_tarski @ A @ ( k1_zfmisc_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X960: $i,X961: $i,X962: $i] :
      ( ~ ( r1_tarski @ ( X960 @ X961 ) )
      | ( r2_hidden @ ( X960 @ X962 ) )
      | ( X962
       != ( k1_zfmisc_1 @ X961 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X960: $i,X961: $i] :
      ( ( r2_hidden @ ( X960 @ ( k1_zfmisc_1 @ X961 ) ) )
      | ~ ( r1_tarski @ ( X960 @ X961 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['0','7'])).

%------------------------------------------------------------------------------
