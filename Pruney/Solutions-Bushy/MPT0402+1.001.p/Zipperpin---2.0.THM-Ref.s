%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fRGm6tLXw2

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:51 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 ( 564 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(t25_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) )
     => ! [D: $i] :
          ~ ( ( r2_hidden @ D @ C )
            & ~ ( r1_tarski @ D @ A )
            & ~ ( r1_tarski @ D @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_setfam_1 @ C @ ( k2_tarski @ A @ B ) )
       => ! [D: $i] :
            ~ ( ( r2_hidden @ D @ C )
              & ~ ( r1_tarski @ D @ A )
              & ~ ( r1_tarski @ D @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_D_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_D_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( sk_D @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_setfam_1 @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_D_2 @ ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r2_hidden @ sk_D_2 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_setfam_1 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ X14 @ X11 )
      | ( X12
       != ( k2_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ X11 )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_xboole_0 @ X13 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
    | ( ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('20',plain,
    ( ( ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_B )
    | ( ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_D_2 @ ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('22',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_B )
    | ( ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_D @ sk_D_2 @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_D_2 @ sk_A ),
    inference(demod,[status(thm)],['5','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).


%------------------------------------------------------------------------------
