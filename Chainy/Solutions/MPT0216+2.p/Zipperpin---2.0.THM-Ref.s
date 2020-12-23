%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0216+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NH45QTn8HG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 171 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t9_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ ( B @ C ) ) )
     => ( B = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ ( B @ C ) ) )
       => ( B = C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A_2 )
    = ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ ( B @ C ) ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X980: $i,X981: $i,X982: $i] :
      ( ( X981 = X980 )
      | ( ( k1_tarski @ X981 )
       != ( k2_tarski @ ( X980 @ X982 ) ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) )
       != ( k2_tarski @ ( X1 @ X0 ) ) )
      | ( sk_A_2 = X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_A_2 = sk_B_2 ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ( k1_tarski @ sk_B_2 )
    = ( k2_tarski @ ( sk_B_2 @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['0','4'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('6',plain,(
    ! [X441: $i,X442: $i,X443: $i,X444: $i] :
      ( ( X442 != X441 )
      | ( r2_hidden @ ( X442 @ X443 ) )
      | ( X443
       != ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X441: $i,X444: $i] :
      ( r2_hidden @ ( X441 @ ( k2_tarski @ ( X444 @ X441 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ ( sk_C_8 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_C_8 = sk_B_2 ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    sk_B_2 != sk_C_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
