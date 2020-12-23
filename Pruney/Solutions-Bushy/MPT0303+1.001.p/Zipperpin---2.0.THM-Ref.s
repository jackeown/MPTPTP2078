%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0303+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LSwP6LUOLz

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  88 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 ( 922 expanded)
%              Number of equality atoms :   22 (  80 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_C @ X2 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X3 = X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X3 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t115_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ A )
        = ( k2_zfmisc_1 @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ A )
          = ( k2_zfmisc_1 @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t115_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 )
      | ( X0 = sk_A )
      | ( X1 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ sk_A @ X1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_C @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_A )
    = ( k2_zfmisc_1 @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B ) @ ( sk_C @ sk_A @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('24',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).


%------------------------------------------------------------------------------
