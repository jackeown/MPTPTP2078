%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0071+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d4zqINpYve

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 ( 373 expanded)
%              Number of equality atoms :   33 (  37 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_D_6_type,type,(
    sk_D_6: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t64_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ D ) )
        & ( r1_xboole_0 @ ( B @ D ) ) )
     => ( r1_xboole_0 @ ( A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_tarski @ ( C @ D ) )
          & ( r1_xboole_0 @ ( B @ D ) ) )
       => ( r1_xboole_0 @ ( A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( sk_C_5 @ sk_D_6 ) ),
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
    ( ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = sk_D_6 ),
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
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = sk_C_5 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_D_6 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X111: $i,X112: $i,X113: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X111 @ X112 ) @ X113 ) )
      = ( k3_xboole_0 @ ( X111 @ ( k3_xboole_0 @ ( X112 @ X113 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_D_6 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('15',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ k1_xboole_0 ) )
      = X122 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X122: $i] :
      ( ( k2_xboole_0 @ ( X122 @ o_0_0_xboole_0 ) )
      = X122 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X129: $i,X130: $i] :
      ( ( k3_xboole_0 @ ( X129 @ ( k2_xboole_0 @ ( X129 @ X130 ) ) ) )
      = X129 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_D_6 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( X0 @ sk_D_6 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','21'])).

thf('23',plain,
    ( o_0_0_xboole_0
    = ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference('sup+',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( r1_xboole_0 @ ( A @ C ) ) ) )).

thf('30',plain,(
    ! [X248: $i,X249: $i,X250: $i] :
      ( ~ ( r1_tarski @ ( X248 @ X249 ) )
      | ~ ( r1_xboole_0 @ ( X249 @ X250 ) )
      | ( r1_xboole_0 @ ( X248 @ X250 ) ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_A_2 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
