%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0292+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gCmI9z7QSk

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:39 EST 2020

% Result     : Theorem 7.79s
% Output     : Refutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :   46 (  93 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  409 ( 921 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X14: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ ( sk_D @ X14 @ X10 ) )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X10: $i,X14: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X10 ) @ X10 )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X10: $i,X14: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X10 ) @ X10 )
      | ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X10: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X15 )
      | ~ ( r2_hidden @ X15 @ X10 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X10: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X15 )
      | ~ ( r2_hidden @ X15 @ X10 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X14 @ X10 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).


%------------------------------------------------------------------------------
