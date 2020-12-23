%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0258+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PB8DGwMImR

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 11.92s
% Output     : Refutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  164 ( 231 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( A @ B ) )
        & ( r2_hidden @ ( C @ B ) ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ ( A @ C ) @ B ) )
        = ( k2_tarski @ ( A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ ( A @ B ) )
          & ( r2_hidden @ ( C @ B ) ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ ( A @ C ) @ B ) )
          = ( k2_tarski @ ( A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ ( sk_C_10 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ C ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X1105: $i,X1107: $i,X1108: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( X1105 @ X1107 ) @ X1108 ) )
      | ~ ( r2_hidden @ ( X1107 @ X1108 ) )
      | ~ ( r2_hidden @ ( X1105 @ X1108 ) ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ sk_B_2 ) )
      | ( r1_tarski @ ( k2_tarski @ ( X0 @ sk_A_2 ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_C_10 @ sk_A_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) @ sk_B_2 ) )
    = ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) ) ) )
    = ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) @ sk_B_2 ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ( k3_xboole_0 @ ( sk_B_2 @ ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) ) ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

%------------------------------------------------------------------------------
