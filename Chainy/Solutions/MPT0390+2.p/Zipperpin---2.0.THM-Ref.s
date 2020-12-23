%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0390+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ccgCvCc2Bp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  172 ( 219 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_23_type,type,(
    sk_C_23: $i )).

thf(sk_B_10_type,type,(
    sk_B_10: $i )).

thf(t8_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ ( A @ B ) )
          & ( r1_tarski @ ( A @ C ) ) )
       => ( r1_tarski @ ( k1_setfam_1 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B_10 @ sk_C_23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X1827: $i,X1828: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X1827 @ X1828 ) )
      | ~ ( r2_hidden @ ( X1828 @ X1827 ) ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B_10 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_setfam_1 @ sk_B_10 @ sk_A_2 ) )
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
    ( ( k2_xboole_0 @ ( sk_A_2 @ ( k1_setfam_1 @ sk_B_10 ) ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('9',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_setfam_1 @ sk_B_10 @ sk_A_2 ) )
    = ( k1_setfam_1 @ sk_B_10 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ ( k1_setfam_1 @ sk_B_10 ) ) )
    = ( k1_setfam_1 @ sk_B_10 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( sk_A_2 @ sk_C_23 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ B ) ) ) )).

thf('15',plain,(
    ! [X125: $i,X126: $i,X127: $i] :
      ( ~ ( r1_tarski @ ( X125 @ X126 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( X125 @ X127 ) @ X126 ) ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) @ sk_C_23 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B_10 @ sk_C_23 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
