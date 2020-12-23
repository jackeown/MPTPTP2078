%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0081+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KOvOjiqp1T

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 193 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t74_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
        & ( r1_xboole_0 @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X111: $i,X112: $i,X113: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X111 @ X112 ) @ X113 ) )
      = ( k3_xboole_0 @ ( X111 @ ( k3_xboole_0 @ ( X112 @ X113 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('8',plain,(
    ! [X155: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X155 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X155: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X155 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('11',plain,(
    ! [X149: $i,X150: $i] :
      ( ( ( k3_xboole_0 @ ( X149 @ X150 ) )
        = X149 )
      | ~ ( r1_tarski @ ( X149 @ X150 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
