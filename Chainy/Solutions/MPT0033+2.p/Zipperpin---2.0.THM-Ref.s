%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0033+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OCWlrFvgYF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 8.05s
% Output     : Refutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  167 ( 187 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t26_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
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
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
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
    ! [X120: $i,X121: $i] :
      ( ( k3_xboole_0 @ ( X120 @ ( k2_xboole_0 @ ( X120 @ X121 ) ) ) )
      = X120 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X102: $i,X103: $i,X104: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X102 @ X103 ) @ X104 ) )
      = ( k3_xboole_0 @ ( X102 @ ( k3_xboole_0 @ ( X103 @ X104 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( sk_A_2 @ X0 ) )
      = ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X107: $i,X108: $i,X109: $i] :
      ( ( r1_tarski @ ( X107 @ X108 ) )
      | ~ ( r1_tarski @ ( X107 @ ( k3_xboole_0 @ ( X108 @ X109 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
