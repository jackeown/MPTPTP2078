%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0851+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Yn1fSOV3Lo

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 4.43s
% Output     : Refutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  216 ( 288 expanded)
%              Number of equality atoms :   41 (  53 expanded)
%              Maximal formula depth    :   14 (   7 average)

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

thf(t7_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
          = B )
        & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t7_mcart_1])).

thf('0',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_B_78 )
    | ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_A_14 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_B_78 )
   <= ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_B_78 ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ ( C @ D ) ) )
             => ( B = D ) ) ) ) )).

thf('2',plain,(
    ! [X3778: $i,X3779: $i,X3780: $i,X3781: $i,X3782: $i,X3783: $i] :
      ( ( X3781
       != ( k2_mcart_1 @ X3778 ) )
      | ( X3781 = X3782 )
      | ( X3778
       != ( k4_tarski @ ( X3783 @ X3782 ) ) )
      | ( X3778
       != ( k4_tarski @ ( X3779 @ X3780 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('3',plain,(
    ! [X3779: $i,X3780: $i,X3782: $i,X3783: $i] :
      ( ( ( k4_tarski @ ( X3783 @ X3782 ) )
       != ( k4_tarski @ ( X3779 @ X3780 ) ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ ( X3783 @ X3782 ) ) )
        = X3782 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X1 @ X0 ) ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ( sk_B_78 != sk_B_78 )
   <= ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_B_78 ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( $false
   <= ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_B_78 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ ( C @ D ) ) )
             => ( B = C ) ) ) ) )).

thf('7',plain,(
    ! [X3771: $i,X3772: $i,X3773: $i,X3774: $i,X3775: $i,X3776: $i] :
      ( ( X3774
       != ( k1_mcart_1 @ X3771 ) )
      | ( X3774 = X3775 )
      | ( X3771
       != ( k4_tarski @ ( X3775 @ X3776 ) ) )
      | ( X3771
       != ( k4_tarski @ ( X3772 @ X3773 ) ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('8',plain,(
    ! [X3772: $i,X3773: $i,X3775: $i,X3776: $i] :
      ( ( ( k4_tarski @ ( X3775 @ X3776 ) )
       != ( k4_tarski @ ( X3772 @ X3773 ) ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ ( X3775 @ X3776 ) ) )
        = X3775 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X1 @ X0 ) ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_A_14 )
   <= ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_A_14 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A_14 != sk_A_14 )
   <= ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_A_14 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
    = sk_A_14 ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_B_78 )
    | ( ( k1_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
     != sk_A_14 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ( k2_mcart_1 @ ( k4_tarski @ ( sk_A_14 @ sk_B_78 ) ) )
 != sk_B_78 ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['6','14'])).

%------------------------------------------------------------------------------
