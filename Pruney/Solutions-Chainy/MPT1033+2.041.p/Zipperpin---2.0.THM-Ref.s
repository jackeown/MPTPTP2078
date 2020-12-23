%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qdVRD14Pkc

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:10 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 247 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  723 (3446 expanded)
%              Number of equality atoms :   60 ( 256 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X25 = X22 )
      | ~ ( r1_partfun1 @ X25 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_partfun1 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('21',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','38'])).

thf('40',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','50'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['51','55'])).

thf('57',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('58',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['19','58'])).

thf('60',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['10','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','60','61'])).

thf('63',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','62'])).

thf('64',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['19','58'])).

thf('72',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['63','64','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['53'])).

thf('77',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qdVRD14Pkc
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 234 iterations in 0.166s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.62  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(t142_funct_2, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ![D:$i]:
% 0.39/0.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62           ( ( r1_partfun1 @ C @ D ) =>
% 0.39/0.62             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.62               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62          ( ![D:$i]:
% 0.39/0.62            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62              ( ( r1_partfun1 @ C @ D ) =>
% 0.39/0.62                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.62                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.39/0.62  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t148_partfun1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ![D:$i]:
% 0.39/0.62         ( ( ( v1_funct_1 @ D ) & 
% 0.39/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.39/0.62               ( r1_partfun1 @ C @ D ) ) =>
% 0.39/0.62             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X22)
% 0.39/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.39/0.62          | ((X25) = (X22))
% 0.39/0.62          | ~ (r1_partfun1 @ X25 @ X22)
% 0.39/0.62          | ~ (v1_partfun1 @ X22 @ X23)
% 0.39/0.62          | ~ (v1_partfun1 @ X25 @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.39/0.62          | ~ (v1_funct_1 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.39/0.62          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.39/0.62          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.39/0.62          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.39/0.62          | ((X0) = (sk_D))
% 0.39/0.62          | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc5_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.62       ( ![C:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.39/0.62             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.39/0.62          | (v1_partfun1 @ X19 @ X20)
% 0.39/0.62          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.39/0.62          | ~ (v1_funct_1 @ X19)
% 0.39/0.62          | (v1_xboole_0 @ X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_B_2)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_2)
% 0.39/0.62        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.62  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('10', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.39/0.62  thf(l13_xboole_0, axiom,
% 0.39/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['14'])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      ((![X0 : $i]:
% 0.39/0.62          (((X0) != (k1_xboole_0))
% 0.39/0.62           | ~ (v1_xboole_0 @ X0)
% 0.39/0.62           | ~ (v1_xboole_0 @ sk_B_2)))
% 0.39/0.62         <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.39/0.62         <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.62  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      ((~ (v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.39/0.62      inference('simplify_reflect+', [status(thm)], ['17', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['14'])).
% 0.39/0.62  thf('21', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.62  thf(t9_mcart_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ~( ( r2_hidden @ B @ A ) & 
% 0.39/0.62                 ( ![C:$i,D:$i]:
% 0.39/0.62                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.39/0.62                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X16 : $i]:
% 0.39/0.62         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X16) @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['14'])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.62  thf(t113_zfmisc_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]:
% 0.39/0.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['25', '27'])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.39/0.62        | ~ (v1_xboole_0 @ sk_A))),
% 0.39/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.62         | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '30'])).
% 0.39/0.62  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf(t5_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.39/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X9 @ X10)
% 0.39/0.62          | ~ (v1_xboole_0 @ X11)
% 0.39/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.62  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['23', '37'])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['22', '38'])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X16 : $i]:
% 0.39/0.62         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X16) @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('split', [status(esa)], ['14'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_D @ 
% 0.39/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup+', [status(thm)], ['41', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X9 @ X10)
% 0.39/0.62          | ~ (v1_xboole_0 @ X11)
% 0.39/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.62  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['40', '49'])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.39/0.62         <= ((((sk_A) = (k1_xboole_0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['39', '50'])).
% 0.39/0.62  thf(t4_subset_1, axiom,
% 0.39/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.62  thf(reflexivity_r2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.39/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.39/0.62      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.39/0.62      inference('condensation', [status(thm)], ['53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['52', '54'])).
% 0.39/0.62  thf('56', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('demod', [status(thm)], ['51', '55'])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.39/0.62      inference('split', [status(esa)], ['14'])).
% 0.39/0.62  thf('58', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.39/0.62      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.39/0.62  thf('59', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['19', '58'])).
% 0.39/0.62  thf('60', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 0.39/0.62      inference('clc', [status(thm)], ['10', '59'])).
% 0.39/0.62  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.39/0.62          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.39/0.62          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.39/0.62          | ((X0) = (sk_D)))),
% 0.39/0.62      inference('demod', [status(thm)], ['4', '60', '61'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      ((((sk_C) = (sk_D))
% 0.39/0.62        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.39/0.62        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '62'])).
% 0.39/0.62  thf('64', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.39/0.62          | (v1_partfun1 @ X19 @ X20)
% 0.39/0.62          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.39/0.62          | ~ (v1_funct_1 @ X19)
% 0.39/0.62          | (v1_xboole_0 @ X21))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_B_2)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.39/0.62        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.62  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('70', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.39/0.62  thf('71', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['19', '58'])).
% 0.39/0.62  thf('72', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.39/0.62      inference('clc', [status(thm)], ['70', '71'])).
% 0.39/0.62  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('74', plain, (((sk_C) = (sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['63', '64', '72', '73'])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.39/0.62      inference('condensation', [status(thm)], ['53'])).
% 0.39/0.62  thf('77', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.62  thf('78', plain, ($false),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '74', '77'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
