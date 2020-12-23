%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0088+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgtFD1QdCq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 15.42s
% Output     : Refutation 15.42s
% Verified   : 
% Statistics : Number of formulae       :   64 (  70 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  415 ( 459 expanded)
%              Number of equality atoms :   34 (  38 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_xboole_0 @ ( B @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
       => ( r1_xboole_0 @ ( B @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('1',plain,(
    ! [X174: $i,X175: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X174 @ X175 ) @ X174 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('2',plain,(
    ! [X149: $i,X150: $i] :
      ( ( ( k3_xboole_0 @ ( X149 @ X150 ) )
        = X149 )
      | ~ ( r1_tarski @ ( X149 @ X150 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X205: $i,X206: $i] :
      ( ( k4_xboole_0 @ ( X205 @ ( k4_xboole_0 @ ( X205 @ X206 ) ) ) )
      = ( k3_xboole_0 @ ( X205 @ X206 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X222: $i,X223: $i,X224: $i] :
      ( ( k4_xboole_0 @ ( X222 @ ( k2_xboole_0 @ ( X223 @ X224 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ ( X222 @ X223 ) @ ( k4_xboole_0 @ ( X222 @ X224 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
      = ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X187: $i,X188: $i,X189: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X187 @ X188 ) @ X189 ) )
      = ( k4_xboole_0 @ ( X187 @ ( k2_xboole_0 @ ( X188 @ X189 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X222: $i,X223: $i,X224: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X222 @ X223 ) @ X224 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ ( X222 @ X223 ) @ ( k4_xboole_0 @ ( X222 @ X224 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
        & ( r1_xboole_0 @ ( A @ B ) ) ) )).

thf('12',plain,(
    ! [X283: $i,X284: $i,X285: $i] :
      ( ~ ( r1_xboole_0 @ ( X283 @ X284 ) )
      | ( r1_xboole_0 @ ( X283 @ ( k3_xboole_0 @ ( X284 @ X285 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_B_2 @ X0 ) @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('17',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( X0 @ sk_C_5 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('19',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ ( C @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X62: $i,X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ ( X64 @ ( k3_xboole_0 @ ( X62 @ X65 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X62 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( X1 @ X0 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( X0 @ sk_C_5 ) ) ) @ sk_A_2 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('27',plain,(
    ! [X111: $i,X112: $i,X113: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X111 @ X112 ) @ X113 ) )
      = ( k3_xboole_0 @ ( X111 @ ( k3_xboole_0 @ ( X112 @ X113 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( X0 @ sk_C_5 ) ) ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['5','29'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
