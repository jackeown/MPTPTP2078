%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CkUfN1Xc1l

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:05 EST 2020

% Result     : Theorem 3.39s
% Output     : Refutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 235 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  704 (3396 expanded)
%              Number of equality atoms :   58 ( 250 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( X42 = X39 )
      | ~ ( r1_partfun1 @ X42 @ X39 )
      | ~ ( v1_partfun1 @ X39 @ X40 )
      | ~ ( v1_partfun1 @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
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
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','32'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','51'])).

thf('53',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('54',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['19','54'])).

thf('56',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['10','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','56','57'])).

thf('59',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['19','54'])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['59','60','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CkUfN1Xc1l
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.39/3.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.39/3.58  % Solved by: fo/fo7.sh
% 3.39/3.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.39/3.58  % done 2775 iterations in 3.124s
% 3.39/3.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.39/3.58  % SZS output start Refutation
% 3.39/3.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.39/3.58  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.39/3.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.39/3.58  thf(sk_D_type, type, sk_D: $i).
% 3.39/3.58  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 3.39/3.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.39/3.58  thf(sk_A_type, type, sk_A: $i).
% 3.39/3.58  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.39/3.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.39/3.58  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 3.39/3.58  thf(sk_C_type, type, sk_C: $i).
% 3.39/3.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.39/3.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.39/3.58  thf(sk_B_type, type, sk_B: $i > $i).
% 3.39/3.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.39/3.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.39/3.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.39/3.58  thf(t142_funct_2, conjecture,
% 3.39/3.58    (![A:$i,B:$i,C:$i]:
% 3.39/3.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.39/3.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58       ( ![D:$i]:
% 3.39/3.58         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.39/3.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58           ( ( r1_partfun1 @ C @ D ) =>
% 3.39/3.58             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.39/3.58               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 3.39/3.58  thf(zf_stmt_0, negated_conjecture,
% 3.39/3.58    (~( ![A:$i,B:$i,C:$i]:
% 3.39/3.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.39/3.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58          ( ![D:$i]:
% 3.39/3.58            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.39/3.58                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58              ( ( r1_partfun1 @ C @ D ) =>
% 3.39/3.58                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.39/3.58                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 3.39/3.58    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 3.39/3.58  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('1', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('2', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf(t148_partfun1, axiom,
% 3.39/3.58    (![A:$i,B:$i,C:$i]:
% 3.39/3.58     ( ( ( v1_funct_1 @ C ) & 
% 3.39/3.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58       ( ![D:$i]:
% 3.39/3.58         ( ( ( v1_funct_1 @ D ) & 
% 3.39/3.58             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 3.39/3.58               ( r1_partfun1 @ C @ D ) ) =>
% 3.39/3.58             ( ( C ) = ( D ) ) ) ) ) ))).
% 3.39/3.58  thf('3', plain,
% 3.39/3.58      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.39/3.58         (~ (v1_funct_1 @ X39)
% 3.39/3.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.39/3.58          | ((X42) = (X39))
% 3.39/3.58          | ~ (r1_partfun1 @ X42 @ X39)
% 3.39/3.58          | ~ (v1_partfun1 @ X39 @ X40)
% 3.39/3.58          | ~ (v1_partfun1 @ X42 @ X40)
% 3.39/3.58          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.39/3.58          | ~ (v1_funct_1 @ X42))),
% 3.39/3.58      inference('cnf', [status(esa)], [t148_partfun1])).
% 3.39/3.58  thf('4', plain,
% 3.39/3.58      (![X0 : $i]:
% 3.39/3.58         (~ (v1_funct_1 @ X0)
% 3.39/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.39/3.58          | ~ (v1_partfun1 @ X0 @ sk_A)
% 3.39/3.58          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 3.39/3.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 3.39/3.58          | ((X0) = (sk_D))
% 3.39/3.58          | ~ (v1_funct_1 @ sk_D))),
% 3.39/3.58      inference('sup-', [status(thm)], ['2', '3'])).
% 3.39/3.58  thf('5', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf(cc5_funct_2, axiom,
% 3.39/3.58    (![A:$i,B:$i]:
% 3.39/3.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.39/3.58       ( ![C:$i]:
% 3.39/3.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.39/3.58           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 3.39/3.58             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 3.39/3.58  thf('6', plain,
% 3.39/3.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.39/3.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.39/3.58          | (v1_partfun1 @ X28 @ X29)
% 3.39/3.58          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 3.39/3.58          | ~ (v1_funct_1 @ X28)
% 3.39/3.58          | (v1_xboole_0 @ X30))),
% 3.39/3.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 3.39/3.58  thf('7', plain,
% 3.39/3.58      (((v1_xboole_0 @ sk_B_1)
% 3.39/3.58        | ~ (v1_funct_1 @ sk_D)
% 3.39/3.58        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 3.39/3.58        | (v1_partfun1 @ sk_D @ sk_A))),
% 3.39/3.58      inference('sup-', [status(thm)], ['5', '6'])).
% 3.39/3.58  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('10', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 3.39/3.58      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.39/3.58  thf(l13_xboole_0, axiom,
% 3.39/3.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.39/3.58  thf('11', plain,
% 3.39/3.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.39/3.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.39/3.58  thf('12', plain,
% 3.39/3.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.39/3.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.39/3.58  thf('13', plain,
% 3.39/3.58      (![X0 : $i, X1 : $i]:
% 3.39/3.58         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.39/3.58      inference('sup+', [status(thm)], ['11', '12'])).
% 3.39/3.58  thf('14', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('15', plain,
% 3.39/3.58      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.39/3.58      inference('split', [status(esa)], ['14'])).
% 3.39/3.58  thf('16', plain,
% 3.39/3.58      ((![X0 : $i]:
% 3.39/3.58          (((X0) != (k1_xboole_0))
% 3.39/3.58           | ~ (v1_xboole_0 @ X0)
% 3.39/3.58           | ~ (v1_xboole_0 @ sk_B_1)))
% 3.39/3.58         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup-', [status(thm)], ['13', '15'])).
% 3.39/3.58  thf('17', plain,
% 3.39/3.58      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.39/3.58         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.39/3.58      inference('simplify', [status(thm)], ['16'])).
% 3.39/3.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.39/3.58  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.39/3.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.39/3.58  thf('19', plain,
% 3.39/3.58      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.39/3.58      inference('simplify_reflect+', [status(thm)], ['17', '18'])).
% 3.39/3.58  thf(t4_subset_1, axiom,
% 3.39/3.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.39/3.58  thf('20', plain,
% 3.39/3.58      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 3.39/3.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.39/3.58  thf(reflexivity_r2_relset_1, axiom,
% 3.39/3.58    (![A:$i,B:$i,C:$i,D:$i]:
% 3.39/3.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.39/3.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.39/3.58       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.39/3.58  thf('21', plain,
% 3.39/3.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.39/3.58         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 3.39/3.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.39/3.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.39/3.58      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.39/3.58  thf('22', plain,
% 3.39/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.39/3.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.39/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.39/3.58      inference('condensation', [status(thm)], ['21'])).
% 3.39/3.58  thf('23', plain,
% 3.39/3.58      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.39/3.58      inference('sup-', [status(thm)], ['20', '22'])).
% 3.39/3.58  thf('24', plain,
% 3.39/3.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('split', [status(esa)], ['14'])).
% 3.39/3.58  thf('25', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('26', plain,
% 3.39/3.58      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup-', [status(thm)], ['24', '25'])).
% 3.39/3.58  thf(t29_mcart_1, axiom,
% 3.39/3.58    (![A:$i]:
% 3.39/3.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.39/3.58          ( ![B:$i]:
% 3.39/3.58            ( ~( ( r2_hidden @ B @ A ) & 
% 3.39/3.58                 ( ![C:$i,D:$i,E:$i]:
% 3.39/3.58                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 3.39/3.58                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 3.39/3.58  thf('27', plain,
% 3.39/3.58      (![X24 : $i]:
% 3.39/3.58         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X24) @ X24))),
% 3.39/3.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 3.39/3.58  thf('28', plain,
% 3.39/3.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('split', [status(esa)], ['14'])).
% 3.39/3.58  thf('29', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('30', plain,
% 3.39/3.58      (((m1_subset_1 @ sk_C @ 
% 3.39/3.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup+', [status(thm)], ['28', '29'])).
% 3.39/3.58  thf(t113_zfmisc_1, axiom,
% 3.39/3.58    (![A:$i,B:$i]:
% 3.39/3.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.39/3.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.39/3.58  thf('31', plain,
% 3.39/3.58      (![X4 : $i, X5 : $i]:
% 3.39/3.58         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 3.39/3.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.39/3.58  thf('32', plain,
% 3.39/3.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 3.39/3.58      inference('simplify', [status(thm)], ['31'])).
% 3.39/3.58  thf('33', plain,
% 3.39/3.58      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('demod', [status(thm)], ['30', '32'])).
% 3.39/3.58  thf(t5_subset, axiom,
% 3.39/3.58    (![A:$i,B:$i,C:$i]:
% 3.39/3.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.39/3.58          ( v1_xboole_0 @ C ) ) ))).
% 3.39/3.58  thf('34', plain,
% 3.39/3.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.39/3.58         (~ (r2_hidden @ X10 @ X11)
% 3.39/3.58          | ~ (v1_xboole_0 @ X12)
% 3.39/3.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.39/3.58      inference('cnf', [status(esa)], [t5_subset])).
% 3.39/3.58  thf('35', plain,
% 3.39/3.58      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C)))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup-', [status(thm)], ['33', '34'])).
% 3.39/3.58  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.39/3.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.39/3.58  thf('37', plain,
% 3.39/3.58      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('demod', [status(thm)], ['35', '36'])).
% 3.39/3.58  thf('38', plain,
% 3.39/3.58      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup-', [status(thm)], ['27', '37'])).
% 3.39/3.58  thf('39', plain,
% 3.39/3.58      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('demod', [status(thm)], ['26', '38'])).
% 3.39/3.58  thf('40', plain,
% 3.39/3.58      (![X24 : $i]:
% 3.39/3.58         (((X24) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X24) @ X24))),
% 3.39/3.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 3.39/3.58  thf('41', plain,
% 3.39/3.58      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('split', [status(esa)], ['14'])).
% 3.39/3.58  thf('42', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('43', plain,
% 3.39/3.58      (((m1_subset_1 @ sk_D @ 
% 3.39/3.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup+', [status(thm)], ['41', '42'])).
% 3.39/3.58  thf('44', plain,
% 3.39/3.58      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 3.39/3.58      inference('simplify', [status(thm)], ['31'])).
% 3.39/3.58  thf('45', plain,
% 3.39/3.58      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('demod', [status(thm)], ['43', '44'])).
% 3.39/3.58  thf('46', plain,
% 3.39/3.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.39/3.58         (~ (r2_hidden @ X10 @ X11)
% 3.39/3.58          | ~ (v1_xboole_0 @ X12)
% 3.39/3.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.39/3.58      inference('cnf', [status(esa)], [t5_subset])).
% 3.39/3.58  thf('47', plain,
% 3.39/3.58      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup-', [status(thm)], ['45', '46'])).
% 3.39/3.58  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.39/3.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.39/3.58  thf('49', plain,
% 3.39/3.58      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('demod', [status(thm)], ['47', '48'])).
% 3.39/3.58  thf('50', plain,
% 3.39/3.58      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('sup-', [status(thm)], ['40', '49'])).
% 3.39/3.58  thf('51', plain,
% 3.39/3.58      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0))
% 3.39/3.58         <= ((((sk_A) = (k1_xboole_0))))),
% 3.39/3.58      inference('demod', [status(thm)], ['39', '50'])).
% 3.39/3.58  thf('52', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.39/3.58      inference('sup-', [status(thm)], ['23', '51'])).
% 3.39/3.58  thf('53', plain,
% 3.39/3.58      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.39/3.58      inference('split', [status(esa)], ['14'])).
% 3.39/3.58  thf('54', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 3.39/3.58      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 3.39/3.58  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.39/3.58      inference('simpl_trail', [status(thm)], ['19', '54'])).
% 3.39/3.58  thf('56', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 3.39/3.58      inference('clc', [status(thm)], ['10', '55'])).
% 3.39/3.58  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('58', plain,
% 3.39/3.58      (![X0 : $i]:
% 3.39/3.58         (~ (v1_funct_1 @ X0)
% 3.39/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.39/3.58          | ~ (v1_partfun1 @ X0 @ sk_A)
% 3.39/3.58          | ~ (r1_partfun1 @ X0 @ sk_D)
% 3.39/3.58          | ((X0) = (sk_D)))),
% 3.39/3.58      inference('demod', [status(thm)], ['4', '56', '57'])).
% 3.39/3.58  thf('59', plain,
% 3.39/3.58      ((((sk_C) = (sk_D))
% 3.39/3.58        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 3.39/3.58        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 3.39/3.58        | ~ (v1_funct_1 @ sk_C))),
% 3.39/3.58      inference('sup-', [status(thm)], ['1', '58'])).
% 3.39/3.58  thf('60', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('61', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('62', plain,
% 3.39/3.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.39/3.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.39/3.58          | (v1_partfun1 @ X28 @ X29)
% 3.39/3.58          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 3.39/3.58          | ~ (v1_funct_1 @ X28)
% 3.39/3.58          | (v1_xboole_0 @ X30))),
% 3.39/3.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 3.39/3.58  thf('63', plain,
% 3.39/3.58      (((v1_xboole_0 @ sk_B_1)
% 3.39/3.58        | ~ (v1_funct_1 @ sk_C)
% 3.39/3.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.39/3.58        | (v1_partfun1 @ sk_C @ sk_A))),
% 3.39/3.58      inference('sup-', [status(thm)], ['61', '62'])).
% 3.39/3.58  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('66', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C @ sk_A))),
% 3.39/3.58      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.39/3.58  thf('67', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.39/3.58      inference('simpl_trail', [status(thm)], ['19', '54'])).
% 3.39/3.58  thf('68', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 3.39/3.58      inference('clc', [status(thm)], ['66', '67'])).
% 3.39/3.58  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('70', plain, (((sk_C) = (sk_D))),
% 3.39/3.58      inference('demod', [status(thm)], ['59', '60', '68', '69'])).
% 3.39/3.58  thf('71', plain,
% 3.39/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.39/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.39/3.58  thf('72', plain,
% 3.39/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.39/3.58         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.39/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.39/3.58      inference('condensation', [status(thm)], ['21'])).
% 3.39/3.58  thf('73', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)),
% 3.39/3.58      inference('sup-', [status(thm)], ['71', '72'])).
% 3.39/3.58  thf('74', plain, ($false),
% 3.39/3.58      inference('demod', [status(thm)], ['0', '70', '73'])).
% 3.39/3.58  
% 3.39/3.58  % SZS output end Refutation
% 3.39/3.58  
% 3.39/3.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
