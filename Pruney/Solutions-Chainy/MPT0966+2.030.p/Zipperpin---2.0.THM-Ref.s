%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zpYCDzbQ7y

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:10 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 787 expanded)
%              Number of leaves         :   30 ( 226 expanded)
%              Depth                    :   21
%              Number of atoms          : 1038 (13076 expanded)
%              Number of equality atoms :   99 ( 938 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['5','8'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( v1_funct_2 @ X18 @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['11','16','17'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','38'])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['39'])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('42',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('44',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    ! [X10: $i] :
      ( zip_tseitin_0 @ X10 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','57','60'])).

thf('62',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['5','8'])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','57','60'])).

thf('72',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12
       != ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X10: $i] :
      ( zip_tseitin_0 @ X10 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('83',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','85','90','91','92'])).

thf('94',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['44','93'])).

thf('95',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['18','94'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','97','91'])).

thf('99',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('101',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['44','93'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['99','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zpYCDzbQ7y
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 160 iterations in 0.174s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.63  thf(t8_funct_2, conjecture,
% 0.47/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.63       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.47/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.63           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.63          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.47/0.63            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.63              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.47/0.63  thf('0', plain,
% 0.47/0.63      ((~ (v1_funct_1 @ sk_D)
% 0.47/0.63        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.47/0.63        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.47/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.63  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('6', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.63  thf('7', plain,
% 0.47/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.63         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.47/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.63  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.47/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.63  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '8'])).
% 0.47/0.63  thf(t4_funct_2, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.63       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.47/0.63         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.47/0.63           ( m1_subset_1 @
% 0.47/0.63             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.47/0.63  thf('10', plain,
% 0.47/0.63      (![X18 : $i, X19 : $i]:
% 0.47/0.63         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.47/0.63          | (v1_funct_2 @ X18 @ (k1_relat_1 @ X18) @ X19)
% 0.47/0.63          | ~ (v1_funct_1 @ X18)
% 0.47/0.63          | ~ (v1_relat_1 @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.63        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.63  thf('12', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(cc2_relat_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.63  thf('13', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.47/0.63          | (v1_relat_1 @ X0)
% 0.47/0.63          | ~ (v1_relat_1 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.47/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.63  thf(fc6_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.63  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.47/0.63  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('18', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.63      inference('demod', [status(thm)], ['11', '16', '17'])).
% 0.47/0.63  thf(d1_funct_2, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_1, axiom,
% 0.47/0.63    (![B:$i,A:$i]:
% 0.47/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.63  thf('19', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i]:
% 0.47/0.63         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.63  thf('20', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i]:
% 0.47/0.63         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i]:
% 0.47/0.63         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.63         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.47/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.63  thf(zf_stmt_3, axiom,
% 0.47/0.63    (![C:$i,B:$i,A:$i]:
% 0.47/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.63  thf(zf_stmt_5, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.63         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.47/0.63          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.47/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.63  thf('25', plain,
% 0.47/0.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((zip_tseitin_0 @ X1 @ X0)
% 0.47/0.63          | ((sk_B) = (X1))
% 0.47/0.63          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['22', '25'])).
% 0.47/0.63  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.63         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.47/0.63          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.47/0.63          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.47/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.63         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.47/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.63      inference('demod', [status(thm)], ['29', '32'])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (((sk_B) = (X0))
% 0.47/0.63          | (zip_tseitin_0 @ X0 @ X1)
% 0.47/0.63          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['26', '33'])).
% 0.47/0.63  thf('35', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('split', [status(esa)], ['35'])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      ((![X0 : $i, X1 : $i]:
% 0.47/0.63          (((X0) != (k1_xboole_0))
% 0.47/0.63           | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.47/0.63           | (zip_tseitin_0 @ X0 @ X1)))
% 0.47/0.63         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['34', '36'])).
% 0.47/0.63  thf('38', plain,
% 0.47/0.63      ((![X1 : $i]:
% 0.47/0.63          ((zip_tseitin_0 @ k1_xboole_0 @ X1) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 0.47/0.63         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.63          ((zip_tseitin_0 @ X0 @ X1)
% 0.47/0.63           | (zip_tseitin_0 @ X0 @ X2)
% 0.47/0.63           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 0.47/0.63         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['19', '38'])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      ((![X0 : $i, X1 : $i]:
% 0.47/0.63          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 0.47/0.63         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('condensation', [status(thm)], ['39'])).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 0.47/0.63         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.63  thf('43', plain,
% 0.47/0.63      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.63      inference('demod', [status(thm)], ['29', '32'])).
% 0.47/0.63  thf('44', plain,
% 0.47/0.63      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.63      inference('clc', [status(thm)], ['42', '43'])).
% 0.47/0.63  thf('45', plain,
% 0.47/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('split', [status(esa)], ['35'])).
% 0.47/0.63  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.63         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.47/0.63          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.47/0.63          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.47/0.63         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('split', [status(esa)], ['35'])).
% 0.47/0.63  thf('51', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('52', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D @ 
% 0.47/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['50', '51'])).
% 0.47/0.63  thf('53', plain,
% 0.47/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.63         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.47/0.63          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.47/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.63  thf('54', plain,
% 0.47/0.63      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.47/0.63         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.63  thf('55', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i]:
% 0.47/0.63         ((zip_tseitin_0 @ X10 @ X11) | ((X11) != (k1_xboole_0)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.63  thf('56', plain, (![X10 : $i]: (zip_tseitin_0 @ X10 @ k1_xboole_0)),
% 0.47/0.63      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.63  thf('57', plain,
% 0.47/0.63      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['54', '56'])).
% 0.47/0.63  thf('58', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D @ 
% 0.47/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['50', '51'])).
% 0.47/0.63  thf('59', plain,
% 0.47/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.63         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.47/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.63  thf('60', plain,
% 0.47/0.63      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.63  thf('61', plain,
% 0.47/0.63      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['49', '57', '60'])).
% 0.47/0.63  thf('62', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '8'])).
% 0.47/0.63  thf('63', plain,
% 0.47/0.63      (![X18 : $i, X19 : $i]:
% 0.47/0.63         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.47/0.63          | (m1_subset_1 @ X18 @ 
% 0.47/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ X19)))
% 0.47/0.63          | ~ (v1_funct_1 @ X18)
% 0.47/0.63          | ~ (v1_relat_1 @ X18))),
% 0.47/0.63      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.47/0.63  thf('64', plain,
% 0.47/0.63      ((~ (v1_relat_1 @ sk_D)
% 0.47/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.47/0.63        | (m1_subset_1 @ sk_D @ 
% 0.47/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.63  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.47/0.63  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('67', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.47/0.63  thf('68', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D @ 
% 0.47/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['61', '67'])).
% 0.47/0.63  thf('69', plain,
% 0.47/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.63         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.47/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.63  thf('70', plain,
% 0.47/0.63      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.63  thf('71', plain,
% 0.47/0.63      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['49', '57', '60'])).
% 0.47/0.63  thf('72', plain,
% 0.47/0.63      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['70', '71'])).
% 0.47/0.63  thf('73', plain,
% 0.47/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.63         (((X12) != (k1_relset_1 @ X12 @ X13 @ X14))
% 0.47/0.63          | (v1_funct_2 @ X14 @ X12 @ X13)
% 0.47/0.63          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.63  thf('74', plain,
% 0.47/0.63      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.63         | ~ (zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)
% 0.47/0.63         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.47/0.63  thf('75', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D @ 
% 0.47/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['61', '67'])).
% 0.47/0.63  thf('76', plain,
% 0.47/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.63         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.47/0.63          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.47/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.63  thf('77', plain,
% 0.47/0.63      ((((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0)
% 0.47/0.63         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.63  thf('78', plain, (![X10 : $i]: (zip_tseitin_0 @ X10 @ k1_xboole_0)),
% 0.47/0.63      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.63  thf('79', plain,
% 0.47/0.63      (((zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['77', '78'])).
% 0.47/0.63  thf('80', plain,
% 0.47/0.63      (((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.63         | (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C)))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['74', '79'])).
% 0.47/0.63  thf('81', plain,
% 0.47/0.63      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['80'])).
% 0.47/0.63  thf('82', plain,
% 0.47/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('split', [status(esa)], ['35'])).
% 0.47/0.63  thf('83', plain,
% 0.47/0.63      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.63         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('84', plain,
% 0.47/0.63      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.47/0.63         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['82', '83'])).
% 0.47/0.63  thf('85', plain,
% 0.47/0.63      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['81', '84'])).
% 0.47/0.63  thf('86', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_D @ 
% 0.47/0.63         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.47/0.63         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['61', '67'])).
% 0.47/0.63  thf('87', plain,
% 0.47/0.63      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('split', [status(esa)], ['35'])).
% 0.47/0.63  thf('88', plain,
% 0.47/0.63      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('89', plain,
% 0.47/0.63      ((~ (m1_subset_1 @ sk_D @ 
% 0.47/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.47/0.63             (((sk_A) = (k1_xboole_0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.63  thf('90', plain,
% 0.47/0.63      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.47/0.63       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['86', '89'])).
% 0.47/0.63  thf('91', plain,
% 0.47/0.63      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.47/0.63       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('92', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.47/0.63      inference('split', [status(esa)], ['35'])).
% 0.47/0.63  thf('93', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['4', '85', '90', '91', '92'])).
% 0.47/0.63  thf('94', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['44', '93'])).
% 0.47/0.63  thf('95', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.47/0.63      inference('demod', [status(thm)], ['18', '94'])).
% 0.47/0.63  thf('96', plain,
% 0.47/0.63      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.63         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('97', plain, (((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.63  thf('98', plain,
% 0.47/0.63      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['4', '97', '91'])).
% 0.47/0.63  thf('99', plain,
% 0.47/0.63      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['1', '98'])).
% 0.47/0.63  thf('100', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ 
% 0.47/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.47/0.63  thf('101', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.63      inference('simpl_trail', [status(thm)], ['44', '93'])).
% 0.47/0.63  thf('102', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['100', '101'])).
% 0.47/0.63  thf('103', plain, ($false), inference('demod', [status(thm)], ['99', '102'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
