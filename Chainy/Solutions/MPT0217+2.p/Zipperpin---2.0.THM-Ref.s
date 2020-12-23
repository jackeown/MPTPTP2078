%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0217+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fhDXb04J7I

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  125 ( 191 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_9_type,type,(
    sk_D_9: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(t10_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( ( k2_tarski @ ( A @ B ) )
          = ( k2_tarski @ ( C @ D ) ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( ( k2_tarski @ ( A @ B ) )
            = ( k2_tarski @ ( C @ D ) ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t10_zfmisc_1])).

thf('0',plain,
    ( ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_tarski @ ( sk_C_8 @ sk_D_9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X441: $i,X442: $i,X443: $i,X444: $i] :
      ( ( X442 != X441 )
      | ( r2_hidden @ ( X442 @ X443 ) )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X441 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_tarski @ ( sk_C_8 @ sk_D_9 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X441: $i,X443: $i,X444: $i,X445: $i] :
      ( ~ ( r2_hidden @ ( X445 @ X443 ) )
      | ( X445 = X444 )
      | ( X445 = X441 )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X441: $i,X444: $i,X445: $i] :
      ( ( X445 = X441 )
      | ( X445 = X444 )
      | ~ ( r2_hidden @ ( X445 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( sk_A_2 = sk_C_8 )
    | ( sk_A_2 = sk_D_9 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    sk_A_2 != sk_D_9 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_A_2 != sk_C_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9','10'])).

%------------------------------------------------------------------------------
