%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0852+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YXJ8A9RSua

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 172 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_78_type,type,(
    sk_B_78: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(t8_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ( ( k4_tarski @ ( k1_mcart_1 @ A @ ( k2_mcart_1 @ A ) ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ ( B @ C ) ) )
       => ( ( k4_tarski @ ( k1_mcart_1 @ A @ ( k2_mcart_1 @ A ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t8_mcart_1])).

thf('0',plain,(
    ( k4_tarski @ ( k1_mcart_1 @ sk_A_14 @ ( k2_mcart_1 @ sk_A_14 ) ) )
 != sk_A_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_B_78 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('2',plain,(
    ! [X3871: $i,X3872: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X3871 @ X3872 ) ) )
      = X3871 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('3',plain,
    ( ( k1_mcart_1 @ sk_A_14 )
    = sk_B_78 ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k4_tarski @ ( sk_B_78 @ ( k2_mcart_1 @ sk_A_14 ) ) )
 != sk_A_14 ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_B_78 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X3871: $i,X3873: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X3871 @ X3873 ) ) )
      = X3873 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( k2_mcart_1 @ sk_A_14 )
    = sk_C_93 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_A_14
    = ( k4_tarski @ ( sk_B_78 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_A_14 != sk_A_14 ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
