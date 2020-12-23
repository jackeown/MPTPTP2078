%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0425+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KI1Pxzbs8U

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:53 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   55 (  62 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  349 ( 435 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t57_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
        & ! [D: $i] :
            ( ( r2_hidden @ D @ B )
           => ( r1_xboole_0 @ D @ C ) ) )
     => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ C @ ( k3_tarski @ ( k2_xboole_0 @ A @ B ) ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ B )
             => ( r1_xboole_0 @ D @ C ) ) )
       => ( r1_tarski @ C @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_C_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ ( k3_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t96_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ ( k3_tarski @ X18 ) @ ( k3_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t96_zfmisc_1])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X20 ) @ X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('15',plain,(
    ! [X22: $i] :
      ( ( r1_xboole_0 @ X22 @ sk_C_1 )
      | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X20 ) @ X21 )
      | ~ ( r1_xboole_0 @ ( sk_C @ X21 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['18'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k3_tarski @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k3_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ ( k3_tarski @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ ( k3_tarski @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_tarski @ ( k2_xboole_0 @ X0 @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ ( k3_tarski @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','28'])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).


%------------------------------------------------------------------------------
