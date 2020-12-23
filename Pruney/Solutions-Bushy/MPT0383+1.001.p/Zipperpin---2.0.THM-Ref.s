%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TVcW9BymWf

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:49 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  275 ( 574 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t65_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r2_hidden @ D @ C )
          & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ A )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( D
                   != ( k4_tarski @ E @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_subset_1])).

thf('0',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( X6
        = ( k4_tarski @ ( sk_E @ X6 @ X5 @ X4 ) @ ( sk_F @ X6 @ X5 @ X4 ) ) )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( X0
        = ( k4_tarski @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( sk_F @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( sk_D
    = ( k4_tarski @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_F @ X6 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ ( sk_F @ sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( sk_F @ sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ sk_B )
      | ( sk_D
       != ( k4_tarski @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_D
       != ( k4_tarski @ X0 @ ( sk_F @ sk_D @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_D != sk_D )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_E @ X6 @ X5 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_E @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('23',plain,(
    m1_subset_1 @ ( sk_E @ sk_D @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_D != sk_D ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).


%------------------------------------------------------------------------------
