%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0020+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K8XbVpNfC2

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 20.94s
% Output     : Refutation 20.94s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  195 ( 268 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t13_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ D ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_tarski @ ( C @ D ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k2_xboole_0 @ ( sk_B_2 @ sk_D_4 ) ) ) ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X110: $i,X111: $i] :
      ( r1_tarski @ ( X110 @ ( k2_xboole_0 @ ( X110 @ X111 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( sk_C_5 @ sk_D_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( sk_C_5 @ sk_D_4 ) )
    = sk_D_4 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('6',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X88 @ X90 ) @ X89 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_D_4 @ X0 ) )
      | ( r1_tarski @ ( sk_C_5 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_D_4 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C_5 @ ( k2_xboole_0 @ ( X0 @ sk_D_4 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X110: $i,X111: $i] :
      ( r1_tarski @ ( X110 @ ( k2_xboole_0 @ ( X110 @ X111 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X88 @ X90 ) @ X89 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_B_2 @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ B ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ B ) ) ) )).

thf('17',plain,(
    ! [X114: $i,X115: $i,X116: $i] :
      ( ~ ( r1_tarski @ ( X114 @ X115 ) )
      | ~ ( r1_tarski @ ( X116 @ X115 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ ( X114 @ X116 ) @ X115 ) ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ X1 ) @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) )
      | ~ ( r1_tarski @ ( X1 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k2_xboole_0 @ ( sk_B_2 @ sk_D_4 ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
