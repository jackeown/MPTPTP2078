%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XPyqBXXxFE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 284 expanded)
%              Number of leaves         :   28 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  720 (3840 expanded)
%              Number of equality atoms :   58 ( 284 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X24 = X21 )
      | ~ ( r1_partfun1 @ X24 @ X21 )
      | ~ ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_partfun1 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( v1_partfun1 @ sk_D @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A_1 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('18',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('19',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    ~ ( r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('36',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','21'])).

thf('46',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_C_1 @ X0 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C_1 )
        | ( X0 = sk_C_1 ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_D = sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_C_1 )
   <= ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','50','54'])).

thf('56',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['23','57'])).

thf('59',plain,(
    v1_partfun1 @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['10','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A_1 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','59','60'])).

thf('62',plain,
    ( ( sk_C_1 = sk_D )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','61'])).

thf('63',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['23','57'])).

thf('71',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A_1 ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_C_1 = sk_D ),
    inference(demod,[status(thm)],['62','63','71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['52'])).

thf('76',plain,(
    r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XPyqBXXxFE
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:39:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 212 iterations in 0.125s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(t142_funct_2, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58       ( ![D:$i]:
% 0.20/0.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58           ( ( r1_partfun1 @ C @ D ) =>
% 0.20/0.58             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.58               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58          ( ![D:$i]:
% 0.20/0.58            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58              ( ( r1_partfun1 @ C @ D ) =>
% 0.20/0.58                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.20/0.58                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.20/0.58  thf('0', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t148_partfun1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58       ( ![D:$i]:
% 0.20/0.58         ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.20/0.58               ( r1_partfun1 @ C @ D ) ) =>
% 0.20/0.58             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.58         (~ (v1_funct_1 @ X21)
% 0.20/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.58          | ((X24) = (X21))
% 0.20/0.58          | ~ (r1_partfun1 @ X24 @ X21)
% 0.20/0.58          | ~ (v1_partfun1 @ X21 @ X22)
% 0.20/0.58          | ~ (v1_partfun1 @ X24 @ X22)
% 0.20/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.20/0.58          | ~ (v1_funct_1 @ X24))),
% 0.20/0.58      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_funct_1 @ X0)
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.20/0.58          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.20/0.58          | ~ (v1_partfun1 @ sk_D @ sk_A_1)
% 0.20/0.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.20/0.58          | ((X0) = (sk_D))
% 0.20/0.58          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc5_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.58       ( ![C:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.58             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.58          | (v1_partfun1 @ X18 @ X19)
% 0.20/0.58          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.20/0.58          | ~ (v1_funct_1 @ X18)
% 0.20/0.58          | (v1_xboole_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B)
% 0.20/0.58        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)
% 0.20/0.58        | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A_1 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.58  thf(l13_xboole_0, axiom,
% 0.20/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf('14', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (((X0) != (k1_xboole_0))
% 0.20/0.58           | ~ (v1_xboole_0 @ X0)
% 0.20/0.58           | ~ (v1_xboole_0 @ sk_B)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.20/0.58         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.58  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.20/0.58  thf('18', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.58  thf('19', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.58  thf('21', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.20/0.58      inference('simplify_reflect+', [status(thm)], ['17', '22'])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['14'])).
% 0.20/0.58  thf('25', plain, (~ (r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_D))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.58  thf(d3_tarski, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X1 : $i, X3 : $i]:
% 0.20/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['14'])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_D @ 
% 0.20/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf(t5_subset, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.20/0.58          | ~ (v1_xboole_0 @ X13)
% 0.20/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.20/0.58           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.58  thf(t113_zfmisc_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i]:
% 0.20/0.58         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.58  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('demod', [status(thm)], ['32', '34', '35'])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      ((![X0 : $i]: (r1_tarski @ sk_D @ X0)) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['27', '36'])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (![X1 : $i, X3 : $i]:
% 0.20/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      ((((sk_A_1) = (k1_xboole_0))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('split', [status(esa)], ['14'])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.20/0.58          | ~ (v1_xboole_0 @ X13)
% 0.20/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      ((![X0 : $i]:
% 0.20/0.58          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.20/0.58           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.58  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      ((![X0 : $i]: (r1_tarski @ sk_C_1 @ X0))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['38', '46'])).
% 0.20/0.58  thf(d10_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (![X5 : $i, X7 : $i]:
% 0.20/0.58         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.20/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      ((![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_1) | ((X0) = (sk_C_1))))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.58  thf('50', plain, ((((sk_D) = (sk_C_1))) <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['37', '49'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.58  thf(reflexivity_r2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.58         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.20/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.58      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.58      inference('condensation', [status(thm)], ['52'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_C_1))
% 0.20/0.58         <= ((((sk_A_1) = (k1_xboole_0))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['51', '53'])).
% 0.20/0.58  thf('55', plain, (~ (((sk_A_1) = (k1_xboole_0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '50', '54'])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A_1) = (k1_xboole_0)))),
% 0.20/0.58      inference('split', [status(esa)], ['14'])).
% 0.20/0.58  thf('57', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.20/0.58  thf('58', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['23', '57'])).
% 0.20/0.58  thf('59', plain, ((v1_partfun1 @ sk_D @ sk_A_1)),
% 0.20/0.58      inference('clc', [status(thm)], ['10', '58'])).
% 0.20/0.58  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_funct_1 @ X0)
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 0.20/0.58          | ~ (v1_partfun1 @ X0 @ sk_A_1)
% 0.20/0.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.20/0.58          | ((X0) = (sk_D)))),
% 0.20/0.58      inference('demod', [status(thm)], ['4', '59', '60'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      ((((sk_C_1) = (sk_D))
% 0.20/0.58        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.20/0.58        | ~ (v1_partfun1 @ sk_C_1 @ sk_A_1)
% 0.20/0.58        | ~ (v1_funct_1 @ sk_C_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '61'])).
% 0.20/0.58  thf('63', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('64', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.58          | (v1_partfun1 @ X18 @ X19)
% 0.20/0.58          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.20/0.58          | ~ (v1_funct_1 @ X18)
% 0.20/0.58          | (v1_xboole_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      (((v1_xboole_0 @ sk_B)
% 0.20/0.58        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B)
% 0.20/0.58        | (v1_partfun1 @ sk_C_1 @ sk_A_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.58  thf('67', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('68', plain, ((v1_funct_2 @ sk_C_1 @ sk_A_1 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('69', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C_1 @ sk_A_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.20/0.58  thf('70', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['23', '57'])).
% 0.20/0.58  thf('71', plain, ((v1_partfun1 @ sk_C_1 @ sk_A_1)),
% 0.20/0.58      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.58  thf('72', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('73', plain, (((sk_C_1) = (sk_D))),
% 0.20/0.58      inference('demod', [status(thm)], ['62', '63', '71', '72'])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('75', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.58      inference('condensation', [status(thm)], ['52'])).
% 0.20/0.58  thf('76', plain, ((r2_relset_1 @ sk_A_1 @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.58  thf('77', plain, ($false),
% 0.20/0.58      inference('demod', [status(thm)], ['0', '73', '76'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
