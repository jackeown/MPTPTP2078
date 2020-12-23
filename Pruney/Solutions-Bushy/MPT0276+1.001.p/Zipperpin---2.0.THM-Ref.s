%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0276+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5XmbEKXrzA

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:38 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   38 (  60 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  326 ( 792 expanded)
%              Number of equality atoms :   32 (  85 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X6 @ X8 ) @ X9 )
        = ( k2_tarski @ X6 @ X8 ) )
      | ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(t74_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != k1_xboole_0 )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k1_tarski @ A ) )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k1_tarski @ B ) )
        & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
         != ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != k1_xboole_0 )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k1_tarski @ A ) )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k1_tarski @ B ) )
          & ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
           != ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_zfmisc_1])).

thf('2',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X4 ) @ X5 )
        = ( k1_tarski @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C )
      | ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ sk_C )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X4 ) @ X5 )
        = ( k1_tarski @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_C )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['8'])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X10 @ X12 ) @ X13 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).


%------------------------------------------------------------------------------
