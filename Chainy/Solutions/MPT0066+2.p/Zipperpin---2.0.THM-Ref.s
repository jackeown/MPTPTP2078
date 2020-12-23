%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0066+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ikdel9jZvq

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  96 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  164 ( 583 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t59_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ C ) ) )
     => ( r2_xboole_0 @ ( A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r2_xboole_0 @ ( B @ C ) ) )
       => ( r2_xboole_0 @ ( A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( X40 @ X41 ) )
      | ~ ( r2_xboole_0 @ ( X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( sk_B_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('5',plain,(
    ! [X100: $i,X101: $i] :
      ( ( ( k2_xboole_0 @ ( X101 @ X100 ) )
        = X100 )
      | ~ ( r1_tarski @ ( X101 @ X100 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ C ) ) ) )).

thf('7',plain,(
    ! [X97: $i,X98: $i,X99: $i] :
      ( ( r1_tarski @ ( X97 @ X98 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( X97 @ X99 ) @ X98 ) ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( sk_B_2 @ X0 ) )
      | ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( sk_A_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('11',plain,
    ( ( sk_A_2 = sk_C_5 )
    | ( r2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_A_2 = sk_C_5 ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_B_2 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( sk_C_5 @ sk_B_2 ) )
    | ( sk_C_5 = sk_B_2 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A_2 = sk_C_5 ),
    inference(clc,[status(thm)],['11','12'])).

thf('19',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_A_2 = sk_C_5 ),
    inference(clc,[status(thm)],['11','12'])).

thf('21',plain,(
    sk_A_2 = sk_B_2 ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    r2_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['14','21'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ ( A @ A ) ) )).

thf('23',plain,(
    ! [X45: $i] :
      ~ ( r2_xboole_0 @ ( X45 @ X45 ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('24',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
