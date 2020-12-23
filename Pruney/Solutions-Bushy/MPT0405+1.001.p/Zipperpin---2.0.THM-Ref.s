%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0405+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZArPJ0rMGP

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 455 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_setfam_1_type,type,(
    k4_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_setfam_1,conjecture,(
    ! [A: $i] :
      ( r1_setfam_1 @ ( k4_setfam_1 @ A @ A ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_setfam_1 @ ( k4_setfam_1 @ A @ A ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t31_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ ( k4_setfam_1 @ sk_A @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d6_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k6_subset_1 @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k6_subset_1 @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_setfam_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ( X16
       != ( k4_setfam_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k4_setfam_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k4_setfam_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X5 @ X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k4_setfam_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k4_setfam_1 @ X0 @ X1 ) )
        = ( k6_subset_1 @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X1 @ X0 ) ) @ X0 @ X1 ) )
      | ( r1_setfam_1 @ ( k4_setfam_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r1_tarski @ ( sk_C @ X3 @ X2 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 )
      | ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k4_setfam_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X2 )
      | ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X0 )
      | ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_setfam_1 @ ( k4_setfam_1 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).


%------------------------------------------------------------------------------
