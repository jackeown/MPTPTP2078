%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g5c8QIwcsS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:59 EST 2020

% Result     : Theorem 2.49s
% Output     : Refutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  137 (7689 expanded)
%              Number of leaves         :   32 (2194 expanded)
%              Depth                    :   22
%              Number of atoms          :  957 (142744 expanded)
%              Number of equality atoms :  114 (11324 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X24 ) @ ( k1_funct_1 @ X24 @ X21 ) )
        = X21 )
      | ~ ( v2_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_D ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15
       != ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('36',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['37'])).

thf('39',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['30','39','42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('59',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['50','51','52','54','55','56','57','58'])).

thf('60',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','59'])).

thf('61',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','59'])).

thf('62',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['27','60','61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X24 ) @ ( k1_funct_1 @ X24 @ X21 ) )
        = X21 )
      | ~ ( v2_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['50','51','52','54','55','56','57','58'])).

thf('73',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['50','51','52','54','55','56','57','58'])).

thf('76',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_D ) )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','78'])).

thf('80',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['50','51','52','54','55','56','57','58'])).

thf('82',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['50','51','52','54','55','56','57','58'])).

thf('83',plain,
    ( ( k1_funct_1 @ k1_xboole_0 @ sk_C )
    = ( k1_funct_1 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','83'])).

thf('86',plain,
    ( ( k1_xboole_0 != sk_D )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
      = sk_D ) ),
    inference(eq_fact,[status(thm)],['85'])).

thf('87',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('89',plain,(
    r2_hidden @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
        = sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_xboole_0 != sk_C )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
      = sk_C ) ),
    inference(eq_fact,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
        = sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('94',plain,
    ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
    = sk_C ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_xboole_0 != sk_D )
    | ( sk_C = sk_D ) ),
    inference(demod,[status(thm)],['86','94'])).

thf('96',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    k1_xboole_0 != sk_D ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_D )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,
    ( ( k1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_funct_1 @ k1_xboole_0 @ sk_C ) )
    = sk_C ),
    inference(clc,[status(thm)],['92','93'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_D )
      | ( sk_C = sk_D ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    sk_C = sk_D ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_C != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g5c8QIwcsS
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:58:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 2.49/2.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.49/2.73  % Solved by: fo/fo7.sh
% 2.49/2.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.49/2.73  % done 1562 iterations in 2.287s
% 2.49/2.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.49/2.73  % SZS output start Refutation
% 2.49/2.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.49/2.73  thf(sk_B_type, type, sk_B: $i).
% 2.49/2.73  thf(sk_C_type, type, sk_C: $i).
% 2.49/2.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.49/2.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.49/2.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.49/2.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.49/2.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.49/2.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.49/2.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.49/2.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.49/2.73  thf(sk_D_type, type, sk_D: $i).
% 2.49/2.73  thf(sk_A_type, type, sk_A: $i).
% 2.49/2.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.49/2.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.49/2.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.49/2.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.49/2.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.49/2.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.49/2.73  thf(t85_funct_2, conjecture,
% 2.49/2.73    (![A:$i,B:$i]:
% 2.49/2.73     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.49/2.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.49/2.73       ( ( v2_funct_1 @ B ) =>
% 2.49/2.73         ( ![C:$i,D:$i]:
% 2.49/2.73           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 2.49/2.73               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 2.49/2.73             ( ( C ) = ( D ) ) ) ) ) ))).
% 2.49/2.73  thf(zf_stmt_0, negated_conjecture,
% 2.49/2.73    (~( ![A:$i,B:$i]:
% 2.49/2.73        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.49/2.73            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.49/2.73          ( ( v2_funct_1 @ B ) =>
% 2.49/2.73            ( ![C:$i,D:$i]:
% 2.49/2.73              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 2.49/2.73                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 2.49/2.73                ( ( C ) = ( D ) ) ) ) ) ) )),
% 2.49/2.73    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 2.49/2.73  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('2', plain,
% 2.49/2.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf(t32_funct_2, axiom,
% 2.49/2.73    (![A:$i,B:$i,C:$i,D:$i]:
% 2.49/2.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.49/2.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.49/2.73       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 2.49/2.73         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.49/2.73           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 2.49/2.73             ( C ) ) ) ) ))).
% 2.49/2.73  thf('3', plain,
% 2.49/2.73      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.49/2.73         (~ (r2_hidden @ X21 @ X22)
% 2.49/2.73          | ((X23) = (k1_xboole_0))
% 2.49/2.73          | ~ (v1_funct_1 @ X24)
% 2.49/2.73          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 2.49/2.73          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ X24) @ (k1_funct_1 @ X24 @ X21))
% 2.49/2.73              = (X21))
% 2.49/2.73          | ~ (v2_funct_1 @ X24))),
% 2.49/2.73      inference('cnf', [status(esa)], [t32_funct_2])).
% 2.49/2.73  thf('4', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (~ (v2_funct_1 @ sk_B)
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0))
% 2.49/2.73              = (X0))
% 2.49/2.73          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.49/2.73          | ~ (v1_funct_1 @ sk_B)
% 2.49/2.73          | ((sk_A) = (k1_xboole_0))
% 2.49/2.73          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.49/2.73      inference('sup-', [status(thm)], ['2', '3'])).
% 2.49/2.73  thf('5', plain, ((v2_funct_1 @ sk_B)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('8', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 2.49/2.73          | ((sk_A) = (k1_xboole_0))
% 2.49/2.73          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.49/2.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.49/2.73  thf('9', plain,
% 2.49/2.73      ((((sk_A) = (k1_xboole_0))
% 2.49/2.73        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 2.49/2.73            = (sk_C)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['1', '8'])).
% 2.49/2.73  thf('10', plain, ((r2_hidden @ sk_D @ sk_A)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('11', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ X0)) = (X0))
% 2.49/2.73          | ((sk_A) = (k1_xboole_0))
% 2.49/2.73          | ~ (r2_hidden @ X0 @ sk_A))),
% 2.49/2.73      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 2.49/2.73  thf('12', plain,
% 2.49/2.73      ((((sk_A) = (k1_xboole_0))
% 2.49/2.73        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_D))
% 2.49/2.73            = (sk_D)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['10', '11'])).
% 2.49/2.73  thf('13', plain, (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('14', plain,
% 2.49/2.73      ((((sk_A) = (k1_xboole_0))
% 2.49/2.73        | ((k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C))
% 2.49/2.73            = (sk_D)))),
% 2.49/2.73      inference('demod', [status(thm)], ['12', '13'])).
% 2.49/2.73  thf('15', plain,
% 2.49/2.73      ((((sk_C) = (sk_D)) | ((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.49/2.73      inference('sup+', [status(thm)], ['9', '14'])).
% 2.49/2.73  thf('16', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_D)))),
% 2.49/2.73      inference('simplify', [status(thm)], ['15'])).
% 2.49/2.73  thf('17', plain, (((sk_C) != (sk_D))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf('19', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 2.49/2.73      inference('demod', [status(thm)], ['0', '18'])).
% 2.49/2.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.49/2.73  thf('20', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.49/2.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.49/2.73  thf(t3_subset, axiom,
% 2.49/2.73    (![A:$i,B:$i]:
% 2.49/2.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.49/2.73  thf('21', plain,
% 2.49/2.73      (![X7 : $i, X9 : $i]:
% 2.49/2.73         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 2.49/2.73      inference('cnf', [status(esa)], [t3_subset])).
% 2.49/2.73  thf('22', plain,
% 2.49/2.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.49/2.73      inference('sup-', [status(thm)], ['20', '21'])).
% 2.49/2.73  thf(redefinition_k1_relset_1, axiom,
% 2.49/2.73    (![A:$i,B:$i,C:$i]:
% 2.49/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.49/2.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.49/2.73  thf('23', plain,
% 2.49/2.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.49/2.73         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 2.49/2.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.49/2.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.49/2.73  thf('24', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i]:
% 2.49/2.73         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.49/2.73      inference('sup-', [status(thm)], ['22', '23'])).
% 2.49/2.73  thf(d1_funct_2, axiom,
% 2.49/2.73    (![A:$i,B:$i,C:$i]:
% 2.49/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.49/2.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.49/2.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.49/2.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.49/2.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.49/2.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.49/2.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.49/2.73  thf(zf_stmt_1, axiom,
% 2.49/2.73    (![C:$i,B:$i,A:$i]:
% 2.49/2.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.49/2.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.49/2.73  thf('25', plain,
% 2.49/2.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.49/2.73         (((X15) != (k1_relset_1 @ X15 @ X16 @ X17))
% 2.49/2.73          | (v1_funct_2 @ X17 @ X15 @ X16)
% 2.49/2.73          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.49/2.73  thf('26', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i]:
% 2.49/2.73         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 2.49/2.73          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 2.49/2.73          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 2.49/2.73      inference('sup-', [status(thm)], ['24', '25'])).
% 2.49/2.73  thf('27', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 2.49/2.73          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 2.49/2.73      inference('simplify', [status(thm)], ['26'])).
% 2.49/2.73  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('29', plain,
% 2.49/2.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.49/2.73         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 2.49/2.73          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 2.49/2.73          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.49/2.73  thf('30', plain,
% 2.49/2.73      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 2.49/2.73        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['28', '29'])).
% 2.49/2.73  thf('31', plain,
% 2.49/2.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.49/2.73  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.49/2.73  thf(zf_stmt_4, axiom,
% 2.49/2.73    (![B:$i,A:$i]:
% 2.49/2.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.49/2.73       ( zip_tseitin_0 @ B @ A ) ))).
% 2.49/2.73  thf(zf_stmt_5, axiom,
% 2.49/2.73    (![A:$i,B:$i,C:$i]:
% 2.49/2.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.49/2.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.49/2.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.49/2.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.49/2.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.49/2.73  thf('32', plain,
% 2.49/2.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.49/2.73         (~ (zip_tseitin_0 @ X18 @ X19)
% 2.49/2.73          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 2.49/2.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.49/2.73  thf('33', plain,
% 2.49/2.73      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 2.49/2.73      inference('sup-', [status(thm)], ['31', '32'])).
% 2.49/2.73  thf('34', plain,
% 2.49/2.73      (![X13 : $i, X14 : $i]:
% 2.49/2.73         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.49/2.73  thf('35', plain,
% 2.49/2.73      (![X13 : $i, X14 : $i]:
% 2.49/2.73         ((zip_tseitin_0 @ X13 @ X14) | ((X14) != (k1_xboole_0)))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.49/2.73  thf('36', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ k1_xboole_0)),
% 2.49/2.73      inference('simplify', [status(thm)], ['35'])).
% 2.49/2.73  thf('37', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.49/2.73         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 2.49/2.73      inference('sup+', [status(thm)], ['34', '36'])).
% 2.49/2.73  thf('38', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 2.49/2.73      inference('eq_fact', [status(thm)], ['37'])).
% 2.49/2.73  thf('39', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 2.49/2.73      inference('demod', [status(thm)], ['33', '38'])).
% 2.49/2.73  thf('40', plain,
% 2.49/2.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('41', plain,
% 2.49/2.73      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.49/2.73         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 2.49/2.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.49/2.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.49/2.73  thf('42', plain,
% 2.49/2.73      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 2.49/2.73      inference('sup-', [status(thm)], ['40', '41'])).
% 2.49/2.73  thf('43', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 2.49/2.73      inference('demod', [status(thm)], ['30', '39', '42'])).
% 2.49/2.73  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf('45', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B))),
% 2.49/2.73      inference('demod', [status(thm)], ['43', '44'])).
% 2.49/2.73  thf('46', plain,
% 2.49/2.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('47', plain,
% 2.49/2.73      (![X7 : $i, X8 : $i]:
% 2.49/2.73         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 2.49/2.73      inference('cnf', [status(esa)], [t3_subset])).
% 2.49/2.73  thf('48', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 2.49/2.73      inference('sup-', [status(thm)], ['46', '47'])).
% 2.49/2.73  thf(d10_xboole_0, axiom,
% 2.49/2.73    (![A:$i,B:$i]:
% 2.49/2.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.49/2.73  thf('49', plain,
% 2.49/2.73      (![X0 : $i, X2 : $i]:
% 2.49/2.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.49/2.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.49/2.73  thf('50', plain,
% 2.49/2.73      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 2.49/2.73        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['48', '49'])).
% 2.49/2.73  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf(t113_zfmisc_1, axiom,
% 2.49/2.73    (![A:$i,B:$i]:
% 2.49/2.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.49/2.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.49/2.73  thf('53', plain,
% 2.49/2.73      (![X5 : $i, X6 : $i]:
% 2.49/2.73         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.49/2.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.49/2.73  thf('54', plain,
% 2.49/2.73      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify', [status(thm)], ['53'])).
% 2.49/2.73  thf('55', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 2.49/2.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.49/2.73  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf('58', plain,
% 2.49/2.73      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify', [status(thm)], ['53'])).
% 2.49/2.73  thf('59', plain, (((k1_xboole_0) = (sk_B))),
% 2.49/2.73      inference('demod', [status(thm)],
% 2.49/2.73                ['50', '51', '52', '54', '55', '56', '57', '58'])).
% 2.49/2.73  thf('60', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.49/2.73      inference('demod', [status(thm)], ['45', '59'])).
% 2.49/2.73  thf('61', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.49/2.73      inference('demod', [status(thm)], ['45', '59'])).
% 2.49/2.73  thf('62', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ k1_xboole_0)),
% 2.49/2.73      inference('simplify', [status(thm)], ['35'])).
% 2.49/2.73  thf('63', plain,
% 2.49/2.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.49/2.73      inference('sup-', [status(thm)], ['20', '21'])).
% 2.49/2.73  thf('64', plain,
% 2.49/2.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.49/2.73         (~ (zip_tseitin_0 @ X18 @ X19)
% 2.49/2.73          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 2.49/2.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.49/2.73  thf('65', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i]:
% 2.49/2.73         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.49/2.73      inference('sup-', [status(thm)], ['63', '64'])).
% 2.49/2.73  thf('66', plain,
% 2.49/2.73      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.49/2.73      inference('sup-', [status(thm)], ['62', '65'])).
% 2.49/2.73  thf('67', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.49/2.73      inference('demod', [status(thm)], ['27', '60', '61', '66'])).
% 2.49/2.73  thf('68', plain,
% 2.49/2.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.49/2.73      inference('sup-', [status(thm)], ['20', '21'])).
% 2.49/2.73  thf('69', plain,
% 2.49/2.73      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.49/2.73         (~ (r2_hidden @ X21 @ X22)
% 2.49/2.73          | ((X23) = (k1_xboole_0))
% 2.49/2.73          | ~ (v1_funct_1 @ X24)
% 2.49/2.73          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 2.49/2.73          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ X24) @ (k1_funct_1 @ X24 @ X21))
% 2.49/2.73              = (X21))
% 2.49/2.73          | ~ (v2_funct_1 @ X24))),
% 2.49/2.73      inference('cnf', [status(esa)], [t32_funct_2])).
% 2.49/2.73  thf('70', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.49/2.73         (~ (v2_funct_1 @ k1_xboole_0)
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73              (k1_funct_1 @ k1_xboole_0 @ X2)) = (X2))
% 2.49/2.73          | ~ (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 2.49/2.73          | ~ (v1_funct_1 @ k1_xboole_0)
% 2.49/2.73          | ((X0) = (k1_xboole_0))
% 2.49/2.73          | ~ (r2_hidden @ X2 @ X1))),
% 2.49/2.73      inference('sup-', [status(thm)], ['68', '69'])).
% 2.49/2.73  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('72', plain, (((k1_xboole_0) = (sk_B))),
% 2.49/2.73      inference('demod', [status(thm)],
% 2.49/2.73                ['50', '51', '52', '54', '55', '56', '57', '58'])).
% 2.49/2.73  thf('73', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.49/2.73      inference('demod', [status(thm)], ['71', '72'])).
% 2.49/2.73  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('75', plain, (((k1_xboole_0) = (sk_B))),
% 2.49/2.73      inference('demod', [status(thm)],
% 2.49/2.73                ['50', '51', '52', '54', '55', '56', '57', '58'])).
% 2.49/2.73  thf('76', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.49/2.73      inference('demod', [status(thm)], ['74', '75'])).
% 2.49/2.73  thf('77', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ X2)) = (X2))
% 2.49/2.73          | ~ (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 2.49/2.73          | ((X0) = (k1_xboole_0))
% 2.49/2.73          | ~ (r2_hidden @ X2 @ X1))),
% 2.49/2.73      inference('demod', [status(thm)], ['70', '73', '76'])).
% 2.49/2.73  thf('78', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i]:
% 2.49/2.73         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 2.49/2.73          | ((X0) = (k1_xboole_0))
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73              (k1_funct_1 @ k1_xboole_0 @ X1)) = (X1)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['67', '77'])).
% 2.49/2.73  thf('79', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_D)) = (sk_D))
% 2.49/2.73          | ((X0) = (k1_xboole_0)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['19', '78'])).
% 2.49/2.73  thf('80', plain, (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('81', plain, (((k1_xboole_0) = (sk_B))),
% 2.49/2.73      inference('demod', [status(thm)],
% 2.49/2.73                ['50', '51', '52', '54', '55', '56', '57', '58'])).
% 2.49/2.73  thf('82', plain, (((k1_xboole_0) = (sk_B))),
% 2.49/2.73      inference('demod', [status(thm)],
% 2.49/2.73                ['50', '51', '52', '54', '55', '56', '57', '58'])).
% 2.49/2.73  thf('83', plain,
% 2.49/2.73      (((k1_funct_1 @ k1_xboole_0 @ sk_C) = (k1_funct_1 @ k1_xboole_0 @ sk_D))),
% 2.49/2.73      inference('demod', [status(thm)], ['80', '81', '82'])).
% 2.49/2.73  thf('84', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_D))
% 2.49/2.73          | ((X0) = (k1_xboole_0)))),
% 2.49/2.73      inference('demod', [status(thm)], ['79', '83'])).
% 2.49/2.73  thf('85', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_D))
% 2.49/2.73          | ((X0) = (k1_xboole_0)))),
% 2.49/2.73      inference('demod', [status(thm)], ['79', '83'])).
% 2.49/2.73  thf('86', plain,
% 2.49/2.73      ((((k1_xboole_0) != (sk_D))
% 2.49/2.73        | ((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_D)))),
% 2.49/2.73      inference('eq_fact', [status(thm)], ['85'])).
% 2.49/2.73  thf('87', plain, ((r2_hidden @ sk_C @ sk_A)),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.49/2.73  thf('89', plain, ((r2_hidden @ sk_C @ k1_xboole_0)),
% 2.49/2.73      inference('demod', [status(thm)], ['87', '88'])).
% 2.49/2.73  thf('90', plain,
% 2.49/2.73      (![X0 : $i, X1 : $i]:
% 2.49/2.73         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 2.49/2.73          | ((X0) = (k1_xboole_0))
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73              (k1_funct_1 @ k1_xboole_0 @ X1)) = (X1)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['67', '77'])).
% 2.49/2.73  thf('91', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_C))
% 2.49/2.73          | ((X0) = (k1_xboole_0)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['89', '90'])).
% 2.49/2.73  thf('92', plain,
% 2.49/2.73      ((((k1_xboole_0) != (sk_C))
% 2.49/2.73        | ((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_C)))),
% 2.49/2.73      inference('eq_fact', [status(thm)], ['91'])).
% 2.49/2.73  thf('93', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73            (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_C))
% 2.49/2.73          | ((X0) = (k1_xboole_0)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['89', '90'])).
% 2.49/2.73  thf('94', plain,
% 2.49/2.73      (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73         (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_C))),
% 2.49/2.73      inference('clc', [status(thm)], ['92', '93'])).
% 2.49/2.73  thf('95', plain, ((((k1_xboole_0) != (sk_D)) | ((sk_C) = (sk_D)))),
% 2.49/2.73      inference('demod', [status(thm)], ['86', '94'])).
% 2.49/2.73  thf('96', plain, (((sk_C) != (sk_D))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('97', plain, (((k1_xboole_0) != (sk_D))),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 2.49/2.73  thf('98', plain,
% 2.49/2.73      (![X0 : $i]:
% 2.49/2.73         (((X0) != (sk_D))
% 2.49/2.73          | ((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73              (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_D)))),
% 2.49/2.73      inference('sup-', [status(thm)], ['84', '97'])).
% 2.49/2.73  thf('99', plain,
% 2.49/2.73      (((k1_funct_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.49/2.73         (k1_funct_1 @ k1_xboole_0 @ sk_C)) = (sk_C))),
% 2.49/2.73      inference('clc', [status(thm)], ['92', '93'])).
% 2.49/2.73  thf('100', plain, (![X0 : $i]: (((X0) != (sk_D)) | ((sk_C) = (sk_D)))),
% 2.49/2.73      inference('demod', [status(thm)], ['98', '99'])).
% 2.49/2.73  thf('101', plain, (((sk_C) = (sk_D))),
% 2.49/2.73      inference('simplify', [status(thm)], ['100'])).
% 2.49/2.73  thf('102', plain, (((sk_C) != (sk_D))),
% 2.49/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.49/2.73  thf('103', plain, ($false),
% 2.49/2.73      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 2.49/2.73  
% 2.49/2.73  % SZS output end Refutation
% 2.49/2.73  
% 2.59/2.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
