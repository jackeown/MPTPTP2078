%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0396+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qx5kW2dveP

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:50 EST 2020

% Result     : Theorem 11.14s
% Output     : Refutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  406 ( 554 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t18_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( sk_D_2 @ X13 @ X10 ) @ X10 )
      | ( X12
       != ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('3',plain,(
    ! [X10: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X13 @ X10 ) @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k3_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ X13 @ ( sk_D_2 @ X13 @ X10 ) )
      | ( X12
       != ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X10: $i,X13: $i] :
      ( ( r2_hidden @ X13 @ ( sk_D_2 @ X13 @ X10 ) )
      | ~ ( r2_hidden @ X13 @ ( k3_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_2 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_D_2 @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).


%------------------------------------------------------------------------------
