%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0016+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cnh00kDj7M

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 4.98s
% Output     : Refutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  228 ( 287 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t9_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ B ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ B ) ) ) )).

thf('5',plain,(
    ! [X106: $i,X107: $i,X108: $i] :
      ( ~ ( r1_tarski @ ( X106 @ X107 ) )
      | ~ ( r1_tarski @ ( X108 @ X107 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ ( X106 @ X108 ) @ X107 ) ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      | ~ ( r1_tarski @ ( X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X102: $i,X103: $i] :
      ( r1_tarski @ ( X102 @ ( k2_xboole_0 @ ( X102 @ X103 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( X1 @ X0 ) @ X0 ) )
      | ( ( k2_xboole_0 @ ( X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X91 @ X92 ) @ X93 ) )
      = ( k2_xboole_0 @ ( X91 @ ( k2_xboole_0 @ ( X92 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_B_2 @ X0 ) )
      = ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_B_2 @ X0 ) )
      = ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X91 @ X92 ) @ X93 ) )
      = ( k2_xboole_0 @ ( X91 @ ( k2_xboole_0 @ ( X92 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X102: $i,X103: $i] :
      ( r1_tarski @ ( X102 @ ( k2_xboole_0 @ ( X102 @ X103 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( X2 @ X1 ) @ ( k2_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ X0 ) @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
