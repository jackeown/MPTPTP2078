%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0037+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2rqF1dR2NQ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 5.11s
% Output     : Refutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 179 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t30_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( C @ B ) ) ) )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ ( A @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( C @ B ) ) ) )
          = ( k3_xboole_0 @ ( k2_xboole_0 @ ( A @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) )
 != ( k3_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('5',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ ( k2_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X127: $i,X128: $i,X129: $i] :
      ( ( k2_xboole_0 @ ( X127 @ ( k3_xboole_0 @ ( X128 @ X129 ) ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( X127 @ X128 ) @ ( k2_xboole_0 @ ( X127 @ X129 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k2_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
