%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0034+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aoZlFtmfgY

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 33.77s
% Output     : Refutation 33.77s
% Verified   : 
% Statistics : Number of formulae       :   47 (  65 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 429 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_6_type,type,(
    sk_D_6: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ D ) ) )
     => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ ( k3_xboole_0 @ ( B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_tarski @ ( C @ D ) ) )
       => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ ( k3_xboole_0 @ ( B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k3_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X107: $i,X108: $i,X109: $i] :
      ( ( r1_tarski @ ( X107 @ X108 ) )
      | ~ ( r1_tarski @ ( X107 @ ( k3_xboole_0 @ ( X108 @ X109 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( sk_C_5 @ sk_D_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = sk_D_6 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('8',plain,(
    ! [X120: $i,X121: $i] :
      ( ( k3_xboole_0 @ ( X120 @ ( k2_xboole_0 @ ( X120 @ X121 ) ) ) )
      = X120 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_D_6 ) )
    = sk_C_5 ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X107: $i,X108: $i,X109: $i] :
      ( ( r1_tarski @ ( X107 @ X108 ) )
      | ~ ( r1_tarski @ ( X107 @ ( k3_xboole_0 @ ( X108 @ X109 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_C_5 ) )
      | ( r1_tarski @ ( X0 @ sk_D_6 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_D_6 ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X91: $i,X92: $i] :
      ( ( ( k2_xboole_0 @ ( X92 @ X91 ) )
        = X91 )
      | ~ ( r1_tarski @ ( X92 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X120: $i,X121: $i] :
      ( ( k3_xboole_0 @ ( X120 @ ( k2_xboole_0 @ ( X120 @ X121 ) ) ) )
      = X120 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
      | ( r1_tarski @ ( X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) ) )
     => ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X110: $i,X111: $i,X112: $i] :
      ( ~ ( r1_tarski @ ( X110 @ X111 ) )
      | ~ ( r1_tarski @ ( X110 @ X112 ) )
      | ( r1_tarski @ ( X110 @ ( k3_xboole_0 @ ( X111 @ X112 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) @ ( k3_xboole_0 @ ( sk_B_2 @ X1 ) ) ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( X0 @ sk_A_2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) @ ( k3_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k3_xboole_0 @ ( sk_B_2 @ sk_D_6 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
