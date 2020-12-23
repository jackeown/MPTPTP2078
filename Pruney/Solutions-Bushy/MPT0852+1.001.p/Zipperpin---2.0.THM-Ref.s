%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0852+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LKesWtEAsi

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  201 ( 321 expanded)
%              Number of equality atoms :   41 (  61 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t8_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t8_mcart_1])).

thf('0',plain,(
    ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k4_tarski @ sk_B @ ( k2_mcart_1 @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = D ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k2_mcart_1 @ X8 ) )
      | ( X11 = X12 )
      | ( X8
       != ( k4_tarski @ X13 @ X12 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ X13 @ X12 )
       != ( k4_tarski @ X9 @ X10 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k4_tarski @ X1 @ X0 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ sk_B @ sk_C_2 ) )
        = sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
       != ( k4_tarski @ X1 @ X0 ) )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_C_2 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A != sk_A )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['6','15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).


%------------------------------------------------------------------------------
