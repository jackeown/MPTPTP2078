%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0035+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0a9MzLLr7w

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  185 ( 262 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t28_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( k3_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).


%------------------------------------------------------------------------------
