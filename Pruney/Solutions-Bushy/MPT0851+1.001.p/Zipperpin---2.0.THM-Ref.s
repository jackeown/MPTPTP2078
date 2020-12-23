%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0851+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3B14JLbMYo

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  216 ( 288 expanded)
%              Number of equality atoms :   41 (  53 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(t7_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
          = B )
        & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t7_mcart_1])).

thf('0',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
    | ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k2_mcart_1 @ X8 ) )
      | ( X11 = X12 )
      | ( X8
       != ( k4_tarski @ X13 @ X12 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ X13 @ X12 )
       != ( k4_tarski @ X9 @ X10 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ( sk_B != sk_B )
   <= ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( $false
   <= ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
    | ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['6','14'])).


%------------------------------------------------------------------------------
