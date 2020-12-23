%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0430+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vWBTIzVA9p

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 7.57s
% Output     : Refutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  133 ( 296 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_24_type,type,(
    sk_C_24: $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(sk_B_12_type,type,(
    sk_B_12: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_4_type,type,(
    sk_A_4: $i )).

thf(t62_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ( ( ( v3_setfam_1 @ ( B @ A ) )
              & ( r1_tarski @ ( C @ B ) ) )
           => ( v3_setfam_1 @ ( C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ( ( ( v3_setfam_1 @ ( B @ A ) )
                & ( r1_tarski @ ( C @ B ) ) )
             => ( v3_setfam_1 @ ( C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_B_12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( ( v3_setfam_1 @ ( B @ A ) )
      <=> ~ ( r2_hidden @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1822: $i,X1823: $i] :
      ( ~ ( v3_setfam_1 @ ( X1823 @ X1822 ) )
      | ~ ( r2_hidden @ ( X1822 @ X1823 ) )
      | ~ ( m1_subset_1 @ ( X1823 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1822 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( sk_A_4 @ sk_B_12 ) )
    | ~ ( v3_setfam_1 @ ( sk_B_12 @ sk_A_4 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ ( sk_C_24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_4 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X1822: $i,X1823: $i] :
      ( ( r2_hidden @ ( X1822 @ X1823 ) )
      | ( v3_setfam_1 @ ( X1823 @ X1822 ) )
      | ~ ( m1_subset_1 @ ( X1823 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1822 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('5',plain,
    ( ( v3_setfam_1 @ ( sk_C_24 @ sk_A_4 ) )
    | ( r2_hidden @ ( sk_A_4 @ sk_C_24 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v3_setfam_1 @ ( sk_C_24 @ sk_A_4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_A_4 @ sk_C_24 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( sk_C_24 @ sk_B_12 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_B_12 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_C_24 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( sk_A_4 @ sk_B_12 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v3_setfam_1 @ ( sk_B_12 @ sk_A_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['2','11','12'])).

%------------------------------------------------------------------------------
