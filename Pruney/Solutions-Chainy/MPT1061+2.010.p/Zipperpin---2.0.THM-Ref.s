%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DfIDNRFrlp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:53 EST 2020

% Result     : Theorem 16.57s
% Output     : Refutation 16.57s
% Verified   : 
% Statistics : Number of formulae       :  208 (2637 expanded)
%              Number of leaves         :   49 ( 787 expanded)
%              Depth                    :   17
%              Number of atoms          : 1617 (48250 expanded)
%              Number of equality atoms :   86 ( 866 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X49 @ X50 @ X48 @ X51 )
        = ( k7_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('16',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['16','19'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','34'])).

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

thf('36',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','33'])).

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

thf('38',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['51','60'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('62',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['31','32'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','66'])).

thf('68',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','34'])).

thf('72',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','72'])).

thf('74',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('79',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','65'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X45 @ X46 @ X44 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['84','85','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('97',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','72'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('103',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('104',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('105',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','72'])).

thf('106',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','103','104','105','106'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','103','104','105','106'])).

thf('109',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('115',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('116',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('117',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('120',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','126'])).

thf('128',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['95','107','108','127'])).

thf('129',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('130',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('132',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('134',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('138',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['136','138'])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['31','32'])).

thf('142',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('144',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['95','107','108','127'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','126'])).

thf('147',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('151',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('153',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['149','155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['74','128','144','145','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DfIDNRFrlp
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 16.57/16.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.57/16.75  % Solved by: fo/fo7.sh
% 16.57/16.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.57/16.75  % done 10053 iterations in 16.294s
% 16.57/16.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.57/16.75  % SZS output start Refutation
% 16.57/16.75  thf(sk_C_type, type, sk_C: $i).
% 16.57/16.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 16.57/16.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 16.57/16.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 16.57/16.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 16.57/16.75  thf(sk_A_type, type, sk_A: $i).
% 16.57/16.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 16.57/16.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.57/16.75  thf(sk_E_type, type, sk_E: $i).
% 16.57/16.75  thf(sk_B_type, type, sk_B: $i).
% 16.57/16.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 16.57/16.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 16.57/16.75  thf(sk_D_type, type, sk_D: $i).
% 16.57/16.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 16.57/16.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 16.57/16.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.57/16.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 16.57/16.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.57/16.75  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 16.57/16.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 16.57/16.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 16.57/16.75  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 16.57/16.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 16.57/16.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 16.57/16.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.57/16.75  thf(t178_funct_2, conjecture,
% 16.57/16.75    (![A:$i,B:$i,C:$i,D:$i]:
% 16.57/16.75     ( ( ~( v1_xboole_0 @ D ) ) =>
% 16.57/16.75       ( ![E:$i]:
% 16.57/16.75         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 16.57/16.75             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 16.57/16.75           ( ( ( r1_tarski @ B @ A ) & 
% 16.57/16.75               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 16.57/16.75             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 16.57/16.75               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 16.57/16.75               ( m1_subset_1 @
% 16.57/16.75                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 16.57/16.75                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 16.57/16.75  thf(zf_stmt_0, negated_conjecture,
% 16.57/16.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 16.57/16.75        ( ( ~( v1_xboole_0 @ D ) ) =>
% 16.57/16.75          ( ![E:$i]:
% 16.57/16.75            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 16.57/16.75                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 16.57/16.75              ( ( ( r1_tarski @ B @ A ) & 
% 16.57/16.75                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 16.57/16.75                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 16.57/16.75                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 16.57/16.75                  ( m1_subset_1 @
% 16.57/16.75                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 16.57/16.75                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 16.57/16.75    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 16.57/16.75  thf('0', plain,
% 16.57/16.75      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 16.57/16.75        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 16.57/16.75             sk_C)
% 16.57/16.75        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('1', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf(redefinition_k2_partfun1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i,D:$i]:
% 16.57/16.75     ( ( ( v1_funct_1 @ C ) & 
% 16.57/16.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.57/16.75       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 16.57/16.75  thf('2', plain,
% 16.57/16.75      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 16.57/16.75         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 16.57/16.75          | ~ (v1_funct_1 @ X48)
% 16.57/16.75          | ((k2_partfun1 @ X49 @ X50 @ X48 @ X51) = (k7_relat_1 @ X48 @ X51)))),
% 16.57/16.75      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 16.57/16.75  thf('3', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 16.57/16.75          | ~ (v1_funct_1 @ sk_E))),
% 16.57/16.75      inference('sup-', [status(thm)], ['1', '2'])).
% 16.57/16.75  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('5', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['3', '4'])).
% 16.57/16.75  thf('6', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf(dt_k2_partfun1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i,D:$i]:
% 16.57/16.75     ( ( ( v1_funct_1 @ C ) & 
% 16.57/16.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 16.57/16.75       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 16.57/16.75         ( m1_subset_1 @
% 16.57/16.75           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 16.57/16.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 16.57/16.75  thf('7', plain,
% 16.57/16.75      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 16.57/16.75         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 16.57/16.75          | ~ (v1_funct_1 @ X44)
% 16.57/16.75          | (v1_funct_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47)))),
% 16.57/16.75      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 16.57/16.75  thf('8', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 16.57/16.75          | ~ (v1_funct_1 @ sk_E))),
% 16.57/16.75      inference('sup-', [status(thm)], ['6', '7'])).
% 16.57/16.75  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('10', plain,
% 16.57/16.75      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['8', '9'])).
% 16.57/16.75  thf('11', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['3', '4'])).
% 16.57/16.75  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['10', '11'])).
% 16.57/16.75  thf('13', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['3', '4'])).
% 16.57/16.75  thf('14', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['3', '4'])).
% 16.57/16.75  thf('15', plain,
% 16.57/16.75      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 16.57/16.75        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 16.57/16.75      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 16.57/16.75  thf('16', plain,
% 16.57/16.75      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('17', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf(redefinition_k7_relset_1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i,D:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.57/16.75       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 16.57/16.75  thf('18', plain,
% 16.57/16.75      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 16.57/16.75         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 16.57/16.75          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 16.57/16.75      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 16.57/16.75  thf('19', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['17', '18'])).
% 16.57/16.75  thf('20', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 16.57/16.75      inference('demod', [status(thm)], ['16', '19'])).
% 16.57/16.75  thf(dt_k7_relat_1, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 16.57/16.75  thf('21', plain,
% 16.57/16.75      (![X12 : $i, X13 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 16.57/16.75      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 16.57/16.75  thf(t148_relat_1, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( v1_relat_1 @ B ) =>
% 16.57/16.75       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 16.57/16.75  thf('22', plain,
% 16.57/16.75      (![X14 : $i, X15 : $i]:
% 16.57/16.75         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 16.57/16.75          | ~ (v1_relat_1 @ X14))),
% 16.57/16.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 16.57/16.75  thf(t87_relat_1, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( v1_relat_1 @ B ) =>
% 16.57/16.75       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 16.57/16.75  thf('23', plain,
% 16.57/16.75      (![X16 : $i, X17 : $i]:
% 16.57/16.75         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X17)) @ X17)
% 16.57/16.75          | ~ (v1_relat_1 @ X16))),
% 16.57/16.75      inference('cnf', [status(esa)], [t87_relat_1])).
% 16.57/16.75  thf(t11_relset_1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i]:
% 16.57/16.75     ( ( v1_relat_1 @ C ) =>
% 16.57/16.75       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 16.57/16.75           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 16.57/16.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 16.57/16.75  thf('24', plain,
% 16.57/16.75      (![X33 : $i, X34 : $i, X35 : $i]:
% 16.57/16.75         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 16.57/16.75          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 16.57/16.75          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 16.57/16.75          | ~ (v1_relat_1 @ X33))),
% 16.57/16.75      inference('cnf', [status(esa)], [t11_relset_1])).
% 16.57/16.75  thf('25', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ X1)
% 16.57/16.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 16.57/16.75          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 16.57/16.75          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 16.57/16.75      inference('sup-', [status(thm)], ['23', '24'])).
% 16.57/16.75  thf('26', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.57/16.75         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 16.57/16.75          | ~ (v1_relat_1 @ X1)
% 16.57/16.75          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 16.57/16.75          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 16.57/16.75          | ~ (v1_relat_1 @ X1))),
% 16.57/16.75      inference('sup-', [status(thm)], ['22', '25'])).
% 16.57/16.75  thf('27', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 16.57/16.75          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 16.57/16.75          | ~ (v1_relat_1 @ X1)
% 16.57/16.75          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))),
% 16.57/16.75      inference('simplify', [status(thm)], ['26'])).
% 16.57/16.75  thf('28', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ X1)
% 16.57/16.75          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 16.57/16.75          | ~ (v1_relat_1 @ X1)
% 16.57/16.75          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2))))),
% 16.57/16.75      inference('sup-', [status(thm)], ['21', '27'])).
% 16.57/16.75  thf('29', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.57/16.75         ((m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 16.57/16.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 16.57/16.75          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 16.57/16.75          | ~ (v1_relat_1 @ X1))),
% 16.57/16.75      inference('simplify', [status(thm)], ['28'])).
% 16.57/16.75  thf('30', plain,
% 16.57/16.75      ((~ (v1_relat_1 @ sk_E)
% 16.57/16.75        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 16.57/16.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 16.57/16.75      inference('sup-', [status(thm)], ['20', '29'])).
% 16.57/16.75  thf('31', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf(cc1_relset_1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.57/16.75       ( v1_relat_1 @ C ) ))).
% 16.57/16.75  thf('32', plain,
% 16.57/16.75      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.57/16.75         ((v1_relat_1 @ X20)
% 16.57/16.75          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 16.57/16.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.57/16.75  thf('33', plain, ((v1_relat_1 @ sk_E)),
% 16.57/16.75      inference('sup-', [status(thm)], ['31', '32'])).
% 16.57/16.75  thf('34', plain,
% 16.57/16.75      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 16.57/16.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 16.57/16.75      inference('demod', [status(thm)], ['30', '33'])).
% 16.57/16.75  thf('35', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 16.57/16.75      inference('demod', [status(thm)], ['15', '34'])).
% 16.57/16.75  thf(d1_funct_2, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.57/16.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 16.57/16.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 16.57/16.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 16.57/16.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 16.57/16.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 16.57/16.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 16.57/16.75  thf(zf_stmt_1, axiom,
% 16.57/16.75    (![B:$i,A:$i]:
% 16.57/16.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 16.57/16.75       ( zip_tseitin_0 @ B @ A ) ))).
% 16.57/16.75  thf('36', plain,
% 16.57/16.75      (![X36 : $i, X37 : $i]:
% 16.57/16.75         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.57/16.75  thf('37', plain,
% 16.57/16.75      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 16.57/16.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 16.57/16.75      inference('demod', [status(thm)], ['30', '33'])).
% 16.57/16.75  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 16.57/16.75  thf(zf_stmt_3, axiom,
% 16.57/16.75    (![C:$i,B:$i,A:$i]:
% 16.57/16.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 16.57/16.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 16.57/16.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 16.57/16.75  thf(zf_stmt_5, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.57/16.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 16.57/16.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 16.57/16.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 16.57/16.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 16.57/16.75  thf('38', plain,
% 16.57/16.75      (![X41 : $i, X42 : $i, X43 : $i]:
% 16.57/16.75         (~ (zip_tseitin_0 @ X41 @ X42)
% 16.57/16.75          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 16.57/16.75          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.57/16.75  thf('39', plain,
% 16.57/16.75      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 16.57/16.75        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 16.57/16.75      inference('sup-', [status(thm)], ['37', '38'])).
% 16.57/16.75  thf('40', plain,
% 16.57/16.75      ((((sk_C) = (k1_xboole_0))
% 16.57/16.75        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 16.57/16.75      inference('sup-', [status(thm)], ['36', '39'])).
% 16.57/16.75  thf('41', plain,
% 16.57/16.75      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 16.57/16.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 16.57/16.75      inference('demod', [status(thm)], ['30', '33'])).
% 16.57/16.75  thf(redefinition_k1_relset_1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.57/16.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 16.57/16.75  thf('42', plain,
% 16.57/16.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.57/16.75         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.57/16.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.57/16.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.57/16.75  thf('43', plain,
% 16.57/16.75      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 16.57/16.75         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 16.57/16.75      inference('sup-', [status(thm)], ['41', '42'])).
% 16.57/16.75  thf('44', plain, ((r1_tarski @ sk_B @ sk_A)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('45', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('46', plain,
% 16.57/16.75      (![X38 : $i, X39 : $i, X40 : $i]:
% 16.57/16.75         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 16.57/16.75          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 16.57/16.75          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 16.57/16.75  thf('47', plain,
% 16.57/16.75      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 16.57/16.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 16.57/16.75      inference('sup-', [status(thm)], ['45', '46'])).
% 16.57/16.75  thf('48', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('49', plain,
% 16.57/16.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.57/16.75         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.57/16.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.57/16.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.57/16.75  thf('50', plain,
% 16.57/16.75      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 16.57/16.75      inference('sup-', [status(thm)], ['48', '49'])).
% 16.57/16.75  thf('51', plain,
% 16.57/16.75      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 16.57/16.75      inference('demod', [status(thm)], ['47', '50'])).
% 16.57/16.75  thf('52', plain,
% 16.57/16.75      (![X36 : $i, X37 : $i]:
% 16.57/16.75         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.57/16.75  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 16.57/16.75  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 16.57/16.75      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 16.57/16.75  thf('54', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 16.57/16.75      inference('sup+', [status(thm)], ['52', '53'])).
% 16.57/16.75  thf('55', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('56', plain,
% 16.57/16.75      (![X41 : $i, X42 : $i, X43 : $i]:
% 16.57/16.75         (~ (zip_tseitin_0 @ X41 @ X42)
% 16.57/16.75          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 16.57/16.75          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.57/16.75  thf('57', plain,
% 16.57/16.75      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 16.57/16.75      inference('sup-', [status(thm)], ['55', '56'])).
% 16.57/16.75  thf('58', plain,
% 16.57/16.75      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 16.57/16.75      inference('sup-', [status(thm)], ['54', '57'])).
% 16.57/16.75  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('60', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 16.57/16.75      inference('clc', [status(thm)], ['58', '59'])).
% 16.57/16.75  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 16.57/16.75      inference('demod', [status(thm)], ['51', '60'])).
% 16.57/16.75  thf(t91_relat_1, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( v1_relat_1 @ B ) =>
% 16.57/16.75       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 16.57/16.75         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 16.57/16.75  thf('62', plain,
% 16.57/16.75      (![X18 : $i, X19 : $i]:
% 16.57/16.75         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 16.57/16.75          | ((k1_relat_1 @ (k7_relat_1 @ X19 @ X18)) = (X18))
% 16.57/16.75          | ~ (v1_relat_1 @ X19))),
% 16.57/16.75      inference('cnf', [status(esa)], [t91_relat_1])).
% 16.57/16.75  thf('63', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (~ (r1_tarski @ X0 @ sk_A)
% 16.57/16.75          | ~ (v1_relat_1 @ sk_E)
% 16.57/16.75          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 16.57/16.75      inference('sup-', [status(thm)], ['61', '62'])).
% 16.57/16.75  thf('64', plain, ((v1_relat_1 @ sk_E)),
% 16.57/16.75      inference('sup-', [status(thm)], ['31', '32'])).
% 16.57/16.75  thf('65', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (~ (r1_tarski @ X0 @ sk_A)
% 16.57/16.75          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 16.57/16.75      inference('demod', [status(thm)], ['63', '64'])).
% 16.57/16.75  thf('66', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 16.57/16.75      inference('sup-', [status(thm)], ['44', '65'])).
% 16.57/16.75  thf('67', plain,
% 16.57/16.75      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 16.57/16.75      inference('demod', [status(thm)], ['43', '66'])).
% 16.57/16.75  thf('68', plain,
% 16.57/16.75      (![X38 : $i, X39 : $i, X40 : $i]:
% 16.57/16.75         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 16.57/16.75          | (v1_funct_2 @ X40 @ X38 @ X39)
% 16.57/16.75          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 16.57/16.75  thf('69', plain,
% 16.57/16.75      ((((sk_B) != (sk_B))
% 16.57/16.75        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 16.57/16.75        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 16.57/16.75      inference('sup-', [status(thm)], ['67', '68'])).
% 16.57/16.75  thf('70', plain,
% 16.57/16.75      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 16.57/16.75        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 16.57/16.75      inference('simplify', [status(thm)], ['69'])).
% 16.57/16.75  thf('71', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 16.57/16.75      inference('demod', [status(thm)], ['15', '34'])).
% 16.57/16.75  thf('72', plain,
% 16.57/16.75      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 16.57/16.75      inference('clc', [status(thm)], ['70', '71'])).
% 16.57/16.75  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['40', '72'])).
% 16.57/16.75  thf('74', plain,
% 16.57/16.75      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 16.57/16.75      inference('demod', [status(thm)], ['35', '73'])).
% 16.57/16.75  thf('75', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 16.57/16.75      inference('sup-', [status(thm)], ['44', '65'])).
% 16.57/16.75  thf(d10_xboole_0, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 16.57/16.75  thf('76', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 16.57/16.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.57/16.75  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.57/16.75      inference('simplify', [status(thm)], ['76'])).
% 16.57/16.75  thf('78', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.57/16.75      inference('simplify', [status(thm)], ['76'])).
% 16.57/16.75  thf('79', plain,
% 16.57/16.75      (![X33 : $i, X34 : $i, X35 : $i]:
% 16.57/16.75         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 16.57/16.75          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 16.57/16.75          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 16.57/16.75          | ~ (v1_relat_1 @ X33))),
% 16.57/16.75      inference('cnf', [status(esa)], [t11_relset_1])).
% 16.57/16.75  thf('80', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ X0)
% 16.57/16.75          | (m1_subset_1 @ X0 @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 16.57/16.75          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 16.57/16.75      inference('sup-', [status(thm)], ['78', '79'])).
% 16.57/16.75  thf('81', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((m1_subset_1 @ X0 @ 
% 16.57/16.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 16.57/16.75          | ~ (v1_relat_1 @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['77', '80'])).
% 16.57/16.75  thf('82', plain,
% 16.57/16.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.57/16.75         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.57/16.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.57/16.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.57/16.75  thf('83', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ X0)
% 16.57/16.75          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 16.57/16.75              = (k1_relat_1 @ X0)))),
% 16.57/16.75      inference('sup-', [status(thm)], ['81', '82'])).
% 16.57/16.75  thf('84', plain,
% 16.57/16.75      ((((k1_relset_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ 
% 16.57/16.75          (k7_relat_1 @ sk_E @ sk_B))
% 16.57/16.75          = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))
% 16.57/16.75        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 16.57/16.75      inference('sup+', [status(thm)], ['75', '83'])).
% 16.57/16.75  thf('85', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 16.57/16.75      inference('sup-', [status(thm)], ['44', '65'])).
% 16.57/16.75  thf('86', plain,
% 16.57/16.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('87', plain,
% 16.57/16.75      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 16.57/16.75         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 16.57/16.75          | ~ (v1_funct_1 @ X44)
% 16.57/16.75          | (m1_subset_1 @ (k2_partfun1 @ X45 @ X46 @ X44 @ X47) @ 
% 16.57/16.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 16.57/16.75      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 16.57/16.75  thf('88', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 16.57/16.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 16.57/16.75          | ~ (v1_funct_1 @ sk_E))),
% 16.57/16.75      inference('sup-', [status(thm)], ['86', '87'])).
% 16.57/16.75  thf('89', plain, ((v1_funct_1 @ sk_E)),
% 16.57/16.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.57/16.75  thf('90', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 16.57/16.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('demod', [status(thm)], ['88', '89'])).
% 16.57/16.75  thf('91', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('demod', [status(thm)], ['3', '4'])).
% 16.57/16.75  thf('92', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 16.57/16.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 16.57/16.75      inference('demod', [status(thm)], ['90', '91'])).
% 16.57/16.75  thf('93', plain,
% 16.57/16.75      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.57/16.75         ((v1_relat_1 @ X20)
% 16.57/16.75          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 16.57/16.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.57/16.75  thf('94', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['92', '93'])).
% 16.57/16.75  thf('95', plain,
% 16.57/16.75      (((k1_relset_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ 
% 16.57/16.75         (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 16.57/16.75      inference('demod', [status(thm)], ['84', '85', '94'])).
% 16.57/16.75  thf('96', plain,
% 16.57/16.75      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 16.57/16.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 16.57/16.75      inference('demod', [status(thm)], ['30', '33'])).
% 16.57/16.75  thf(t3_subset, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 16.57/16.75  thf('97', plain,
% 16.57/16.75      (![X7 : $i, X8 : $i]:
% 16.57/16.75         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 16.57/16.75      inference('cnf', [status(esa)], [t3_subset])).
% 16.57/16.75  thf('98', plain,
% 16.57/16.75      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 16.57/16.75      inference('sup-', [status(thm)], ['96', '97'])).
% 16.57/16.75  thf('99', plain,
% 16.57/16.75      (![X0 : $i, X2 : $i]:
% 16.57/16.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 16.57/16.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.57/16.75  thf('100', plain,
% 16.57/16.75      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_C) @ (k7_relat_1 @ sk_E @ sk_B))
% 16.57/16.75        | ((k2_zfmisc_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_E @ sk_B)))),
% 16.57/16.75      inference('sup-', [status(thm)], ['98', '99'])).
% 16.57/16.75  thf('101', plain, (((sk_C) = (k1_xboole_0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['40', '72'])).
% 16.57/16.75  thf(t113_zfmisc_1, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 16.57/16.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 16.57/16.75  thf('102', plain,
% 16.57/16.75      (![X5 : $i, X6 : $i]:
% 16.57/16.75         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 16.57/16.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 16.57/16.75  thf('103', plain,
% 16.57/16.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 16.57/16.75      inference('simplify', [status(thm)], ['102'])).
% 16.57/16.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 16.57/16.75  thf('104', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 16.57/16.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 16.57/16.75  thf('105', plain, (((sk_C) = (k1_xboole_0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['40', '72'])).
% 16.57/16.75  thf('106', plain,
% 16.57/16.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 16.57/16.75      inference('simplify', [status(thm)], ['102'])).
% 16.57/16.75  thf('107', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 16.57/16.75      inference('demod', [status(thm)],
% 16.57/16.75                ['100', '101', '103', '104', '105', '106'])).
% 16.57/16.75  thf('108', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 16.57/16.75      inference('demod', [status(thm)],
% 16.57/16.75                ['100', '101', '103', '104', '105', '106'])).
% 16.57/16.75  thf('109', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 16.57/16.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 16.57/16.75  thf('110', plain,
% 16.57/16.75      (![X7 : $i, X9 : $i]:
% 16.57/16.75         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 16.57/16.75      inference('cnf', [status(esa)], [t3_subset])).
% 16.57/16.75  thf('111', plain,
% 16.57/16.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['109', '110'])).
% 16.57/16.75  thf('112', plain,
% 16.57/16.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 16.57/16.75         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 16.57/16.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 16.57/16.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 16.57/16.75  thf('113', plain,
% 16.57/16.75      (![X0 : $i, X1 : $i]:
% 16.57/16.75         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['111', '112'])).
% 16.57/16.75  thf('114', plain,
% 16.57/16.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['109', '110'])).
% 16.57/16.75  thf(cc2_relset_1, axiom,
% 16.57/16.75    (![A:$i,B:$i,C:$i]:
% 16.57/16.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 16.57/16.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 16.57/16.75  thf('115', plain,
% 16.57/16.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 16.57/16.75         ((v4_relat_1 @ X23 @ X24)
% 16.57/16.75          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 16.57/16.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 16.57/16.75  thf('116', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 16.57/16.75      inference('sup-', [status(thm)], ['114', '115'])).
% 16.57/16.75  thf(d18_relat_1, axiom,
% 16.57/16.75    (![A:$i,B:$i]:
% 16.57/16.75     ( ( v1_relat_1 @ B ) =>
% 16.57/16.75       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 16.57/16.75  thf('117', plain,
% 16.57/16.75      (![X10 : $i, X11 : $i]:
% 16.57/16.75         (~ (v4_relat_1 @ X10 @ X11)
% 16.57/16.75          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 16.57/16.75          | ~ (v1_relat_1 @ X10))),
% 16.57/16.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 16.57/16.75  thf('118', plain,
% 16.57/16.75      (![X0 : $i]:
% 16.57/16.75         (~ (v1_relat_1 @ k1_xboole_0)
% 16.57/16.75          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['116', '117'])).
% 16.57/16.75  thf('119', plain,
% 16.57/16.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.57/16.75      inference('sup-', [status(thm)], ['109', '110'])).
% 16.57/16.75  thf('120', plain,
% 16.57/16.75      (![X20 : $i, X21 : $i, X22 : $i]:
% 16.57/16.75         ((v1_relat_1 @ X20)
% 16.57/16.75          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 16.57/16.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 16.57/16.75  thf('121', plain, ((v1_relat_1 @ k1_xboole_0)),
% 16.57/16.75      inference('sup-', [status(thm)], ['119', '120'])).
% 16.57/16.75  thf('122', plain,
% 16.57/16.75      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 16.57/16.75      inference('demod', [status(thm)], ['118', '121'])).
% 16.57/16.75  thf('123', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 16.57/16.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 16.57/16.75  thf('124', plain,
% 16.57/16.75      (![X0 : $i, X2 : $i]:
% 16.57/16.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 16.57/16.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.57/16.75  thf('125', plain,
% 16.57/16.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 16.57/16.76      inference('sup-', [status(thm)], ['123', '124'])).
% 16.57/16.76  thf('126', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['122', '125'])).
% 16.57/16.76  thf('127', plain,
% 16.57/16.76      (![X0 : $i, X1 : $i]:
% 16.57/16.76         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 16.57/16.76      inference('demod', [status(thm)], ['113', '126'])).
% 16.57/16.76  thf('128', plain, (((k1_xboole_0) = (sk_B))),
% 16.57/16.76      inference('demod', [status(thm)], ['95', '107', '108', '127'])).
% 16.57/16.76  thf('129', plain,
% 16.57/16.76      (![X12 : $i, X13 : $i]:
% 16.57/16.76         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 16.57/16.76      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 16.57/16.76  thf('130', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 16.57/16.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 16.57/16.76  thf('131', plain,
% 16.57/16.76      (![X0 : $i]:
% 16.57/16.76         (~ (r1_tarski @ X0 @ sk_A)
% 16.57/16.76          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 16.57/16.76      inference('demod', [status(thm)], ['63', '64'])).
% 16.57/16.76  thf('132', plain,
% 16.57/16.76      (((k1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)) = (k1_xboole_0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['130', '131'])).
% 16.57/16.76  thf('133', plain,
% 16.57/16.76      (![X0 : $i]:
% 16.57/16.76         ((m1_subset_1 @ X0 @ 
% 16.57/16.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 16.57/16.76          | ~ (v1_relat_1 @ X0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['77', '80'])).
% 16.57/16.76  thf('134', plain,
% 16.57/16.76      (![X7 : $i, X8 : $i]:
% 16.57/16.76         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 16.57/16.76      inference('cnf', [status(esa)], [t3_subset])).
% 16.57/16.76  thf('135', plain,
% 16.57/16.76      (![X0 : $i]:
% 16.57/16.76         (~ (v1_relat_1 @ X0)
% 16.57/16.76          | (r1_tarski @ X0 @ 
% 16.57/16.76             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 16.57/16.76      inference('sup-', [status(thm)], ['133', '134'])).
% 16.57/16.76  thf('136', plain,
% 16.57/16.76      (((r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ 
% 16.57/16.76         (k2_zfmisc_1 @ k1_xboole_0 @ 
% 16.57/16.76          (k2_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0))))
% 16.57/16.76        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 16.57/16.76      inference('sup+', [status(thm)], ['132', '135'])).
% 16.57/16.76  thf('137', plain,
% 16.57/16.76      (![X5 : $i, X6 : $i]:
% 16.57/16.76         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 16.57/16.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 16.57/16.76  thf('138', plain,
% 16.57/16.76      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 16.57/16.76      inference('simplify', [status(thm)], ['137'])).
% 16.57/16.76  thf('139', plain,
% 16.57/16.76      (((r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ k1_xboole_0)
% 16.57/16.76        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 16.57/16.76      inference('demod', [status(thm)], ['136', '138'])).
% 16.57/16.76  thf('140', plain,
% 16.57/16.76      ((~ (v1_relat_1 @ sk_E)
% 16.57/16.76        | (r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ k1_xboole_0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['129', '139'])).
% 16.57/16.76  thf('141', plain, ((v1_relat_1 @ sk_E)),
% 16.57/16.76      inference('sup-', [status(thm)], ['31', '32'])).
% 16.57/16.76  thf('142', plain,
% 16.57/16.76      ((r1_tarski @ (k7_relat_1 @ sk_E @ k1_xboole_0) @ k1_xboole_0)),
% 16.57/16.76      inference('demod', [status(thm)], ['140', '141'])).
% 16.57/16.76  thf('143', plain,
% 16.57/16.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 16.57/16.76      inference('sup-', [status(thm)], ['123', '124'])).
% 16.57/16.76  thf('144', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['142', '143'])).
% 16.57/16.76  thf('145', plain, (((k1_xboole_0) = (sk_B))),
% 16.57/16.76      inference('demod', [status(thm)], ['95', '107', '108', '127'])).
% 16.57/16.76  thf('146', plain,
% 16.57/16.76      (![X0 : $i, X1 : $i]:
% 16.57/16.76         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 16.57/16.76      inference('demod', [status(thm)], ['113', '126'])).
% 16.57/16.76  thf('147', plain,
% 16.57/16.76      (![X38 : $i, X39 : $i, X40 : $i]:
% 16.57/16.76         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 16.57/16.76          | (v1_funct_2 @ X40 @ X38 @ X39)
% 16.57/16.76          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 16.57/16.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 16.57/16.76  thf('148', plain,
% 16.57/16.76      (![X0 : $i, X1 : $i]:
% 16.57/16.76         (((X1) != (k1_xboole_0))
% 16.57/16.76          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 16.57/16.76          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['146', '147'])).
% 16.57/16.76  thf('149', plain,
% 16.57/16.76      (![X0 : $i]:
% 16.57/16.76         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 16.57/16.76          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 16.57/16.76      inference('simplify', [status(thm)], ['148'])).
% 16.57/16.76  thf('150', plain,
% 16.57/16.76      (![X36 : $i, X37 : $i]:
% 16.57/16.76         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 16.57/16.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 16.57/16.76  thf('151', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 16.57/16.76      inference('simplify', [status(thm)], ['150'])).
% 16.57/16.76  thf('152', plain,
% 16.57/16.76      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 16.57/16.76      inference('sup-', [status(thm)], ['109', '110'])).
% 16.57/16.76  thf('153', plain,
% 16.57/16.76      (![X41 : $i, X42 : $i, X43 : $i]:
% 16.57/16.76         (~ (zip_tseitin_0 @ X41 @ X42)
% 16.57/16.76          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 16.57/16.76          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 16.57/16.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 16.57/16.76  thf('154', plain,
% 16.57/16.76      (![X0 : $i, X1 : $i]:
% 16.57/16.76         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 16.57/16.76      inference('sup-', [status(thm)], ['152', '153'])).
% 16.57/16.76  thf('155', plain,
% 16.57/16.76      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 16.57/16.76      inference('sup-', [status(thm)], ['151', '154'])).
% 16.57/16.76  thf('156', plain,
% 16.57/16.76      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 16.57/16.76      inference('demod', [status(thm)], ['149', '155'])).
% 16.57/16.76  thf('157', plain, ($false),
% 16.57/16.76      inference('demod', [status(thm)], ['74', '128', '144', '145', '156'])).
% 16.57/16.76  
% 16.57/16.76  % SZS output end Refutation
% 16.57/16.76  
% 16.57/16.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
