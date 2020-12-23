%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0070+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gBUCZvpSa3

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 ( 430 expanded)
%              Number of equality atoms :   41 (  55 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( r1_xboole_0 @ ( A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_xboole_0 @ ( B @ C ) ) )
       => ( r1_xboole_0 @ ( A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X100: $i,X101: $i] :
      ( ( ( k2_xboole_0 @ ( X101 @ X100 ) )
        = X100 )
      | ~ ( r1_tarski @ ( X101 @ X100 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('4',plain,(
    ! [X129: $i,X130: $i] :
      ( ( k3_xboole_0 @ ( X129 @ ( k2_xboole_0 @ ( X129 @ X130 ) ) ) )
      = X129 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X111: $i,X112: $i,X113: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X111 @ X112 ) @ X113 ) )
      = ( k3_xboole_0 @ ( X111 @ ( k3_xboole_0 @ ( X112 @ X113 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('14',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ k1_xboole_0 ) )
      = X122 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ o_0_0_xboole_0 ) )
      = X122 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X129: $i,X130: $i] :
      ( ( k3_xboole_0 @ ( X129 @ ( k2_xboole_0 @ ( X129 @ X130 ) ) ) )
      = X129 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( X1 @ X0 ) )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X111: $i,X112: $i,X113: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X111 @ X112 ) @ X113 ) )
      = ( k3_xboole_0 @ ( X111 @ ( k3_xboole_0 @ ( X112 @ X113 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_C_5 @ ( k3_xboole_0 @ ( X0 @ sk_B_2 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['5','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('36',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
