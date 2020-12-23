%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0367+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hk1jEXUYhz

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  133 ( 176 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t48_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ B )
               => ( r2_hidden @ D @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ B )
                 => ( r2_hidden @ D @ C ) )
             => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( r2_hidden @ X9 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X9 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['0','10'])).


%------------------------------------------------------------------------------
