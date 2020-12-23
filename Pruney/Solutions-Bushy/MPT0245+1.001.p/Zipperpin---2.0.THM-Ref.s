%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0245+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TKqOxJirEI

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:34 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   17 (  21 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   73 ( 121 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t40_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r2_hidden @ C @ A )
        | ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( r2_hidden @ C @ A )
          | ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r2_hidden @ C @ A )
        | ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[l2_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5'])).


%------------------------------------------------------------------------------
