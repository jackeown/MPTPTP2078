%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0022+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ovON3bXzeF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 107 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t15_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( A @ B ) )
          = k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t15_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(fc4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X81: $i,X82: $i] :
      ( ( v1_xboole_0 @ X81 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( X81 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc4_xboole_0])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('6',plain,(
    v1_xboole_0 @ sk_A_2 ),
    inference(demod,[status(thm)],['4','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A_2 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

%------------------------------------------------------------------------------
