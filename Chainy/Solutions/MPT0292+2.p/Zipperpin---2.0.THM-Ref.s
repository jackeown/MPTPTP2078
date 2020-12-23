%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0292+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zhhD1oL9zS

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 32.07s
% Output     : Refutation 32.07s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  180 ( 190 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_10_type,type,(
    sk_C_10: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A_2 ) )
 != sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X1219: $i] :
      ( r1_tarski @ ( k1_tarski @ X1219 @ ( k1_zfmisc_1 @ X1219 ) ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X993: $i,X994: $i] :
      ( ( r2_hidden @ ( X993 @ X994 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X993 @ X994 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( A @ ( k3_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1030: $i,X1031: $i] :
      ( ( r1_tarski @ ( X1030 @ ( k3_tarski @ X1031 ) ) )
      | ~ ( r2_hidden @ ( X1030 @ X1031 ) ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) @ X0 ) )
      | ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r1_tarski @ ( C @ B ) ) )
     => ( r1_tarski @ ( k3_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X1237: $i,X1238: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X1237 @ X1238 ) )
      | ( r2_hidden @ ( sk_C_10 @ ( X1238 @ X1237 ) @ X1237 ) ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X961: $i,X962: $i,X963: $i] :
      ( ~ ( r2_hidden @ ( X963 @ X962 ) )
      | ( r1_tarski @ ( X963 @ X961 ) )
      | ( X962
       != ( k1_zfmisc_1 @ X961 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X961: $i,X963: $i] :
      ( ( r1_tarski @ ( X963 @ X961 ) )
      | ~ ( r2_hidden @ ( X963 @ ( k1_zfmisc_1 @ X961 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) @ X1 ) )
      | ( r1_tarski @ ( sk_C_10 @ ( X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1237: $i,X1238: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X1237 @ X1238 ) )
      | ~ ( r1_tarski @ ( sk_C_10 @ ( X1238 @ X1237 ) @ X1238 ) ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) @ X0 ) )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    sk_A_2 != sk_A_2 ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
