%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0335+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7HH6cMNOxE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 3.18s
% Output     : Refutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  337 ( 535 expanded)
%              Number of equality atoms :   42 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_13_type,type,(
    sk_C_13: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_14_type,type,(
    sk_D_14: $i )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( ( k3_xboole_0 @ ( B @ C ) )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ ( D @ A ) ) )
     => ( ( k3_xboole_0 @ ( A @ C ) )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( ( k3_xboole_0 @ ( B @ C ) )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ ( D @ A ) ) )
       => ( ( k3_xboole_0 @ ( A @ C ) )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ ( sk_D_14 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X1017: $i,X1019: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1017 @ X1019 ) )
      | ~ ( r2_hidden @ ( X1017 @ X1019 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_14 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D_14 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('7',plain,(
    ! [X278: $i,X279: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( X278 @ X279 ) @ ( k4_xboole_0 @ ( X278 @ X279 ) ) ) )
      = X278 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_14 @ sk_A_2 ) @ o_0_0_xboole_0 ) )
    = ( k1_tarski @ sk_D_14 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( sk_B_4 @ sk_C_13 ) )
    = ( k1_tarski @ sk_D_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_4 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k4_xboole_0 @ ( X91 @ ( k3_xboole_0 @ ( X92 @ X93 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X91 @ X92 ) @ ( k4_xboole_0 @ ( X91 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_4 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('16',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_4 @ X0 ) ) ) )
      = ( k4_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_D_14 ) ) )
    = ( k4_xboole_0 @ ( sk_A_2 @ sk_C_13 ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k4_xboole_0 @ ( X266 @ ( k4_xboole_0 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_13 ) ) ) )
    = ( k3_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_D_14 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k4_xboole_0 @ ( X266 @ ( k4_xboole_0 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( sk_C_13 @ sk_A_2 ) )
    = ( k3_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_D_14 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('30',plain,
    ( ( k3_xboole_0 @ ( sk_C_13 @ sk_A_2 ) )
    = ( k1_tarski @ sk_D_14 ) ),
    inference(demod,[status(thm)],['8','9','27','28','29'])).

thf('31',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ sk_C_13 ) )
 != ( k1_tarski @ sk_D_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ( k3_xboole_0 @ ( sk_C_13 @ sk_A_2 ) )
 != ( k1_tarski @ sk_D_14 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','33'])).

%------------------------------------------------------------------------------
