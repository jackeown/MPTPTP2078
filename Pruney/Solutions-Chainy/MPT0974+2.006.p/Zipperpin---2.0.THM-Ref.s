%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H0oyNvTxaH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:40 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 154 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  866 (3267 expanded)
%              Number of equality atoms :   58 ( 241 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7','16'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['22','29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['45','47','52','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','56'])).

thf('58',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('60',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H0oyNvTxaH
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.03/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.21  % Solved by: fo/fo7.sh
% 1.03/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.21  % done 553 iterations in 0.752s
% 1.03/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.21  % SZS output start Refutation
% 1.03/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.03/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.03/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.21  thf(sk_C_type, type, sk_C: $i).
% 1.03/1.21  thf(sk_D_type, type, sk_D: $i).
% 1.03/1.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.03/1.21  thf(sk_E_type, type, sk_E: $i).
% 1.03/1.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.03/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.03/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.21  thf(t20_funct_2, conjecture,
% 1.03/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.21       ( ![E:$i]:
% 1.03/1.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.03/1.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.21           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.03/1.21               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.03/1.21             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.03/1.21               ( ( k2_relset_1 @
% 1.03/1.21                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.03/1.21                 ( C ) ) ) ) ) ) ))).
% 1.03/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.21    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.21        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.21            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.21          ( ![E:$i]:
% 1.03/1.21            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.03/1.21                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.03/1.21              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.03/1.21                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.03/1.21                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.03/1.21                  ( ( k2_relset_1 @
% 1.03/1.21                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.03/1.21                    ( C ) ) ) ) ) ) ) )),
% 1.03/1.21    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 1.03/1.21  thf('0', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('1', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(dt_k1_partfun1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.03/1.21     ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.21         ( v1_funct_1 @ F ) & 
% 1.03/1.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.03/1.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.03/1.21         ( m1_subset_1 @
% 1.03/1.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.03/1.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.03/1.21  thf('2', plain,
% 1.03/1.21      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.03/1.21          | ~ (v1_funct_1 @ X22)
% 1.03/1.21          | ~ (v1_funct_1 @ X25)
% 1.03/1.21          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.03/1.21          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.03/1.21  thf('3', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.03/1.21          | ~ (v1_funct_1 @ X1)
% 1.03/1.21          | ~ (v1_funct_1 @ sk_D))),
% 1.03/1.21      inference('sup-', [status(thm)], ['1', '2'])).
% 1.03/1.21  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('5', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.03/1.21          | ~ (v1_funct_1 @ X1))),
% 1.03/1.21      inference('demod', [status(thm)], ['3', '4'])).
% 1.03/1.21  thf('6', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ sk_E)
% 1.03/1.21        | (m1_subset_1 @ 
% 1.03/1.21           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['0', '5'])).
% 1.03/1.21  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('8', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('9', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(redefinition_k1_partfun1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.03/1.21     ( ( ( v1_funct_1 @ E ) & 
% 1.03/1.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.03/1.21         ( v1_funct_1 @ F ) & 
% 1.03/1.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.03/1.21       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.03/1.21  thf('10', plain,
% 1.03/1.21      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.03/1.21          | ~ (v1_funct_1 @ X28)
% 1.03/1.21          | ~ (v1_funct_1 @ X31)
% 1.03/1.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.03/1.21          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 1.03/1.21              = (k5_relat_1 @ X28 @ X31)))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.03/1.21  thf('11', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.03/1.21            = (k5_relat_1 @ sk_D @ X0))
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.21          | ~ (v1_funct_1 @ X0)
% 1.03/1.21          | ~ (v1_funct_1 @ sk_D))),
% 1.03/1.21      inference('sup-', [status(thm)], ['9', '10'])).
% 1.03/1.21  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('13', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.03/1.21            = (k5_relat_1 @ sk_D @ X0))
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.03/1.21          | ~ (v1_funct_1 @ X0))),
% 1.03/1.21      inference('demod', [status(thm)], ['11', '12'])).
% 1.03/1.21  thf('14', plain,
% 1.03/1.21      ((~ (v1_funct_1 @ sk_E)
% 1.03/1.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.03/1.21            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['8', '13'])).
% 1.03/1.21  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('16', plain,
% 1.03/1.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.03/1.21         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.03/1.21      inference('demod', [status(thm)], ['14', '15'])).
% 1.03/1.21  thf('17', plain,
% 1.03/1.21      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.03/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.03/1.21      inference('demod', [status(thm)], ['6', '7', '16'])).
% 1.03/1.21  thf(redefinition_k2_relset_1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.03/1.21  thf('18', plain,
% 1.03/1.21      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.03/1.21         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.21  thf('19', plain,
% 1.03/1.21      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.03/1.21         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['17', '18'])).
% 1.03/1.21  thf('20', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(d1_funct_2, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.03/1.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.03/1.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.03/1.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.03/1.21  thf(zf_stmt_1, axiom,
% 1.03/1.21    (![C:$i,B:$i,A:$i]:
% 1.03/1.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.03/1.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.21  thf('21', plain,
% 1.03/1.21      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.03/1.21         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 1.03/1.21          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 1.03/1.21          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.21  thf('22', plain,
% 1.03/1.21      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.03/1.21        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['20', '21'])).
% 1.03/1.21  thf(zf_stmt_2, axiom,
% 1.03/1.21    (![B:$i,A:$i]:
% 1.03/1.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.21       ( zip_tseitin_0 @ B @ A ) ))).
% 1.03/1.21  thf('23', plain,
% 1.03/1.21      (![X14 : $i, X15 : $i]:
% 1.03/1.21         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.03/1.21  thf('24', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.03/1.21  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.03/1.21  thf(zf_stmt_5, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.03/1.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.03/1.21  thf('25', plain,
% 1.03/1.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.03/1.21         (~ (zip_tseitin_0 @ X19 @ X20)
% 1.03/1.21          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 1.03/1.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.21  thf('26', plain,
% 1.03/1.21      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.03/1.21      inference('sup-', [status(thm)], ['24', '25'])).
% 1.03/1.21  thf('27', plain,
% 1.03/1.21      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.03/1.21      inference('sup-', [status(thm)], ['23', '26'])).
% 1.03/1.21  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('29', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.03/1.21      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 1.03/1.21  thf('30', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(redefinition_k1_relset_1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.03/1.21  thf('31', plain,
% 1.03/1.21      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.03/1.21         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.03/1.21          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.21  thf('32', plain,
% 1.03/1.21      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.03/1.21      inference('sup-', [status(thm)], ['30', '31'])).
% 1.03/1.21  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.03/1.21      inference('demod', [status(thm)], ['22', '29', '32'])).
% 1.03/1.21  thf('34', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('35', plain,
% 1.03/1.21      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.03/1.21         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.21  thf('36', plain,
% 1.03/1.21      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.03/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 1.03/1.21  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.03/1.21      inference('sup+', [status(thm)], ['36', '37'])).
% 1.03/1.21  thf(t47_relat_1, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ( v1_relat_1 @ A ) =>
% 1.03/1.21       ( ![B:$i]:
% 1.03/1.21         ( ( v1_relat_1 @ B ) =>
% 1.03/1.21           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.03/1.21             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.03/1.21  thf('39', plain,
% 1.03/1.21      (![X3 : $i, X4 : $i]:
% 1.03/1.21         (~ (v1_relat_1 @ X3)
% 1.03/1.21          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ X4)) = (k2_relat_1 @ X4))
% 1.03/1.21          | ~ (r1_tarski @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X3))
% 1.03/1.21          | ~ (v1_relat_1 @ X4))),
% 1.03/1.21      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.03/1.21  thf('40', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 1.03/1.21          | ~ (v1_relat_1 @ sk_D))),
% 1.03/1.21      inference('sup-', [status(thm)], ['38', '39'])).
% 1.03/1.21  thf('41', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(cc1_relset_1, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.21       ( v1_relat_1 @ C ) ))).
% 1.03/1.21  thf('42', plain,
% 1.03/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.21         ((v1_relat_1 @ X5)
% 1.03/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.21  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.03/1.21      inference('sup-', [status(thm)], ['41', '42'])).
% 1.03/1.21  thf('44', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.03/1.21          | ~ (v1_relat_1 @ X0)
% 1.03/1.21          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 1.03/1.21      inference('demod', [status(thm)], ['40', '43'])).
% 1.03/1.21  thf('45', plain,
% 1.03/1.21      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.03/1.21        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 1.03/1.21        | ~ (v1_relat_1 @ sk_E))),
% 1.03/1.21      inference('sup-', [status(thm)], ['33', '44'])).
% 1.03/1.21  thf(d10_xboole_0, axiom,
% 1.03/1.21    (![A:$i,B:$i]:
% 1.03/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.03/1.21  thf('46', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.03/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.03/1.21  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.03/1.21      inference('simplify', [status(thm)], ['46'])).
% 1.03/1.21  thf('48', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('49', plain,
% 1.03/1.21      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.03/1.21         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.03/1.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.03/1.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.03/1.21  thf('50', plain,
% 1.03/1.21      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 1.03/1.21      inference('sup-', [status(thm)], ['48', '49'])).
% 1.03/1.21  thf('51', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('52', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.03/1.21      inference('sup+', [status(thm)], ['50', '51'])).
% 1.03/1.21  thf('53', plain,
% 1.03/1.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('54', plain,
% 1.03/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.21         ((v1_relat_1 @ X5)
% 1.03/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.03/1.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.03/1.21  thf('55', plain, ((v1_relat_1 @ sk_E)),
% 1.03/1.21      inference('sup-', [status(thm)], ['53', '54'])).
% 1.03/1.21  thf('56', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.03/1.21      inference('demod', [status(thm)], ['45', '47', '52', '55'])).
% 1.03/1.21  thf('57', plain,
% 1.03/1.21      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.03/1.21      inference('demod', [status(thm)], ['19', '56'])).
% 1.03/1.21  thf('58', plain,
% 1.03/1.21      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.03/1.21         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('59', plain,
% 1.03/1.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.03/1.21         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.03/1.21      inference('demod', [status(thm)], ['14', '15'])).
% 1.03/1.21  thf('60', plain,
% 1.03/1.21      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.03/1.21      inference('demod', [status(thm)], ['58', '59'])).
% 1.03/1.21  thf('61', plain, ($false),
% 1.03/1.21      inference('simplify_reflect-', [status(thm)], ['57', '60'])).
% 1.03/1.21  
% 1.03/1.21  % SZS output end Refutation
% 1.03/1.21  
% 1.03/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
