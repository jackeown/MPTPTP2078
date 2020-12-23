%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0091+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zh1kPth2TR

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   98 ( 142 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t84_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_xboole_0 @ ( A @ C ) )
        & ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( A @ C ) )
          & ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_xboole_0 @ ( B @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X306: $i,X307: $i,X308: $i] :
      ( ( r1_xboole_0 @ ( X306 @ ( k4_xboole_0 @ ( X307 @ X308 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X307 @ ( k4_xboole_0 @ ( X306 @ X308 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('3',plain,(
    r1_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X311: $i,X312: $i] :
      ( ( ( k4_xboole_0 @ ( X311 @ X312 ) )
        = X311 )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('8',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
