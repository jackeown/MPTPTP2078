%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P2GNaNJtz8

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:04 EST 2020

% Result     : Theorem 17.23s
% Output     : Refutation 17.23s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 422 expanded)
%              Number of leaves         :   50 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          : 1379 (8009 expanded)
%              Number of equality atoms :   82 ( 367 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ X45 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1 ),
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13','14','31'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10
        = ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X10 @ X7 ) @ ( sk_D @ X10 @ X7 ) ) @ X7 )
      | ( r2_hidden @ ( sk_C @ X10 @ X7 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['34','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13','14','31'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('54',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X49 @ X46 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('57',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X44 ) @ X45 )
      | ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( v1_funct_2 @ sk_D_2 @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('60',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('62',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['69'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['65','77'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('79',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( ( k7_partfun1 @ X37 @ X36 @ X35 )
        = ( k1_funct_1 @ X36 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['80','83','84'])).

thf('86',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','85'])).

thf('87',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('90',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42 ) @ X41 )
        = ( k1_funct_1 @ X42 @ ( k1_funct_1 @ X38 @ X41 ) ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X39 @ X40 @ X38 ) @ ( k1_relset_1 @ X40 @ X43 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('94',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('101',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['88','105'])).

thf('107',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['87','106'])).

thf('108',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_E )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['46','109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P2GNaNJtz8
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.23/17.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.23/17.46  % Solved by: fo/fo7.sh
% 17.23/17.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.23/17.46  % done 12924 iterations in 16.996s
% 17.23/17.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.23/17.46  % SZS output start Refutation
% 17.23/17.46  thf(sk_E_type, type, sk_E: $i).
% 17.23/17.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.23/17.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.23/17.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.23/17.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.23/17.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 17.23/17.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.23/17.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.23/17.46  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 17.23/17.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 17.23/17.46  thf(sk_F_type, type, sk_F: $i).
% 17.23/17.46  thf(sk_D_2_type, type, sk_D_2: $i).
% 17.23/17.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 17.23/17.46  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 17.23/17.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.23/17.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 17.23/17.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 17.23/17.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.23/17.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.23/17.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 17.23/17.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.23/17.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 17.23/17.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.23/17.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.23/17.46  thf(sk_A_type, type, sk_A: $i).
% 17.23/17.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 17.23/17.46  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 17.23/17.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.23/17.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.23/17.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.23/17.46  thf(t186_funct_2, conjecture,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( ~( v1_xboole_0 @ C ) ) =>
% 17.23/17.46       ( ![D:$i]:
% 17.23/17.46         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 17.23/17.46             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 17.23/17.46           ( ![E:$i]:
% 17.23/17.46             ( ( ( v1_funct_1 @ E ) & 
% 17.23/17.46                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 17.23/17.46               ( ![F:$i]:
% 17.23/17.46                 ( ( m1_subset_1 @ F @ B ) =>
% 17.23/17.46                   ( ( r1_tarski @
% 17.23/17.46                       ( k2_relset_1 @ B @ C @ D ) @ 
% 17.23/17.46                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 17.23/17.46                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 17.23/17.46                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 17.23/17.46                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 17.23/17.46  thf(zf_stmt_0, negated_conjecture,
% 17.23/17.46    (~( ![A:$i,B:$i,C:$i]:
% 17.23/17.46        ( ( ~( v1_xboole_0 @ C ) ) =>
% 17.23/17.46          ( ![D:$i]:
% 17.23/17.46            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 17.23/17.46                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 17.23/17.46              ( ![E:$i]:
% 17.23/17.46                ( ( ( v1_funct_1 @ E ) & 
% 17.23/17.46                    ( m1_subset_1 @
% 17.23/17.46                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 17.23/17.46                  ( ![F:$i]:
% 17.23/17.46                    ( ( m1_subset_1 @ F @ B ) =>
% 17.23/17.46                      ( ( r1_tarski @
% 17.23/17.46                          ( k2_relset_1 @ B @ C @ D ) @ 
% 17.23/17.46                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 17.23/17.46                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 17.23/17.46                          ( ( k1_funct_1 @
% 17.23/17.46                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 17.23/17.46                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 17.23/17.46    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 17.23/17.46  thf('0', plain,
% 17.23/17.46      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) @ 
% 17.23/17.46        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('1', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(redefinition_k1_relset_1, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.23/17.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.23/17.46  thf('2', plain,
% 17.23/17.46      (![X21 : $i, X22 : $i, X23 : $i]:
% 17.23/17.46         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 17.23/17.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 17.23/17.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.23/17.46  thf('3', plain,
% 17.23/17.46      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('sup-', [status(thm)], ['1', '2'])).
% 17.23/17.46  thf('4', plain,
% 17.23/17.46      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) @ 
% 17.23/17.46        (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('demod', [status(thm)], ['0', '3'])).
% 17.23/17.46  thf('5', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(redefinition_k2_relset_1, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.23/17.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 17.23/17.46  thf('6', plain,
% 17.23/17.46      (![X24 : $i, X25 : $i, X26 : $i]:
% 17.23/17.46         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 17.23/17.46          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 17.23/17.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 17.23/17.46  thf('7', plain,
% 17.23/17.46      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 17.23/17.46      inference('sup-', [status(thm)], ['5', '6'])).
% 17.23/17.46  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('demod', [status(thm)], ['4', '7'])).
% 17.23/17.46  thf(t4_funct_2, axiom,
% 17.23/17.46    (![A:$i,B:$i]:
% 17.23/17.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 17.23/17.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 17.23/17.46         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 17.23/17.46           ( m1_subset_1 @
% 17.23/17.46             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 17.23/17.46  thf('9', plain,
% 17.23/17.46      (![X44 : $i, X45 : $i]:
% 17.23/17.46         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 17.23/17.46          | (m1_subset_1 @ X44 @ 
% 17.23/17.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ X45)))
% 17.23/17.46          | ~ (v1_funct_1 @ X44)
% 17.23/17.46          | ~ (v1_relat_1 @ X44))),
% 17.23/17.46      inference('cnf', [status(esa)], [t4_funct_2])).
% 17.23/17.46  thf('10', plain,
% 17.23/17.46      ((~ (v1_relat_1 @ sk_D_2)
% 17.23/17.46        | ~ (v1_funct_1 @ sk_D_2)
% 17.23/17.46        | (m1_subset_1 @ sk_D_2 @ 
% 17.23/17.46           (k1_zfmisc_1 @ 
% 17.23/17.46            (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E)))))),
% 17.23/17.46      inference('sup-', [status(thm)], ['8', '9'])).
% 17.23/17.46  thf('11', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(cc1_relset_1, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.23/17.46       ( v1_relat_1 @ C ) ))).
% 17.23/17.46  thf('12', plain,
% 17.23/17.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 17.23/17.46         ((v1_relat_1 @ X12)
% 17.23/17.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 17.23/17.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.23/17.46  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 17.23/17.46      inference('sup-', [status(thm)], ['11', '12'])).
% 17.23/17.46  thf('14', plain, ((v1_funct_1 @ sk_D_2)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('15', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(d1_funct_2, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.23/17.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.23/17.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.23/17.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.23/17.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.23/17.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.23/17.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.23/17.46  thf(zf_stmt_1, axiom,
% 17.23/17.46    (![C:$i,B:$i,A:$i]:
% 17.23/17.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.23/17.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.23/17.46  thf('16', plain,
% 17.23/17.46      (![X29 : $i, X30 : $i, X31 : $i]:
% 17.23/17.46         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 17.23/17.46          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 17.23/17.46          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.23/17.46  thf('17', plain,
% 17.23/17.46      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 17.23/17.46        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['15', '16'])).
% 17.23/17.46  thf('18', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('19', plain,
% 17.23/17.46      (![X21 : $i, X22 : $i, X23 : $i]:
% 17.23/17.46         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 17.23/17.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 17.23/17.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.23/17.46  thf('20', plain,
% 17.23/17.46      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 17.23/17.46      inference('sup-', [status(thm)], ['18', '19'])).
% 17.23/17.46  thf('21', plain,
% 17.23/17.46      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 17.23/17.46        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 17.23/17.46      inference('demod', [status(thm)], ['17', '20'])).
% 17.23/17.46  thf('22', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.23/17.46  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 17.23/17.46  thf(zf_stmt_4, axiom,
% 17.23/17.46    (![B:$i,A:$i]:
% 17.23/17.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.23/17.46       ( zip_tseitin_0 @ B @ A ) ))).
% 17.23/17.46  thf(zf_stmt_5, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.23/17.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.23/17.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.23/17.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.23/17.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.23/17.46  thf('23', plain,
% 17.23/17.46      (![X32 : $i, X33 : $i, X34 : $i]:
% 17.23/17.46         (~ (zip_tseitin_0 @ X32 @ X33)
% 17.23/17.46          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 17.23/17.46          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.23/17.46  thf('24', plain,
% 17.23/17.46      (((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)
% 17.23/17.46        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 17.23/17.46      inference('sup-', [status(thm)], ['22', '23'])).
% 17.23/17.46  thf('25', plain,
% 17.23/17.46      (![X27 : $i, X28 : $i]:
% 17.23/17.46         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_4])).
% 17.23/17.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 17.23/17.46  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.23/17.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.23/17.46  thf('27', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 17.23/17.46      inference('sup+', [status(thm)], ['25', '26'])).
% 17.23/17.46  thf('28', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('29', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 17.23/17.46      inference('sup-', [status(thm)], ['27', '28'])).
% 17.23/17.46  thf('30', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_1 @ sk_B_1)),
% 17.23/17.46      inference('demod', [status(thm)], ['24', '29'])).
% 17.23/17.46  thf('31', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 17.23/17.46      inference('demod', [status(thm)], ['21', '30'])).
% 17.23/17.46  thf('32', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ 
% 17.23/17.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E))))),
% 17.23/17.46      inference('demod', [status(thm)], ['10', '13', '14', '31'])).
% 17.23/17.46  thf(cc4_relset_1, axiom,
% 17.23/17.46    (![A:$i,B:$i]:
% 17.23/17.46     ( ( v1_xboole_0 @ A ) =>
% 17.23/17.46       ( ![C:$i]:
% 17.23/17.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 17.23/17.46           ( v1_xboole_0 @ C ) ) ) ))).
% 17.23/17.46  thf('33', plain,
% 17.23/17.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 17.23/17.46         (~ (v1_xboole_0 @ X18)
% 17.23/17.46          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 17.23/17.46          | (v1_xboole_0 @ X19))),
% 17.23/17.46      inference('cnf', [status(esa)], [cc4_relset_1])).
% 17.23/17.46  thf('34', plain,
% 17.23/17.46      (((v1_xboole_0 @ sk_D_2) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_E)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['32', '33'])).
% 17.23/17.46  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.23/17.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.23/17.46  thf(d4_relat_1, axiom,
% 17.23/17.46    (![A:$i,B:$i]:
% 17.23/17.46     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 17.23/17.46       ( ![C:$i]:
% 17.23/17.46         ( ( r2_hidden @ C @ B ) <=>
% 17.23/17.46           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 17.23/17.46  thf('36', plain,
% 17.23/17.46      (![X7 : $i, X10 : $i]:
% 17.23/17.46         (((X10) = (k1_relat_1 @ X7))
% 17.23/17.46          | (r2_hidden @ (k4_tarski @ (sk_C @ X10 @ X7) @ (sk_D @ X10 @ X7)) @ 
% 17.23/17.46             X7)
% 17.23/17.46          | (r2_hidden @ (sk_C @ X10 @ X7) @ X10))),
% 17.23/17.46      inference('cnf', [status(esa)], [d4_relat_1])).
% 17.23/17.46  thf(d1_xboole_0, axiom,
% 17.23/17.46    (![A:$i]:
% 17.23/17.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 17.23/17.46  thf('37', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 17.23/17.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 17.23/17.46  thf('38', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]:
% 17.23/17.46         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 17.23/17.46          | ((X1) = (k1_relat_1 @ X0))
% 17.23/17.46          | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('sup-', [status(thm)], ['36', '37'])).
% 17.23/17.46  thf('39', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 17.23/17.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 17.23/17.46  thf('40', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]:
% 17.23/17.46         (~ (v1_xboole_0 @ X1)
% 17.23/17.46          | ((X0) = (k1_relat_1 @ X1))
% 17.23/17.46          | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('sup-', [status(thm)], ['38', '39'])).
% 17.23/17.46  thf('41', plain,
% 17.23/17.46      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('sup-', [status(thm)], ['35', '40'])).
% 17.23/17.46  thf('42', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 17.23/17.46      inference('demod', [status(thm)], ['21', '30'])).
% 17.23/17.46  thf('43', plain, ((((sk_B_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_D_2))),
% 17.23/17.46      inference('sup+', [status(thm)], ['41', '42'])).
% 17.23/17.46  thf('44', plain, (((sk_B_1) != (k1_xboole_0))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('45', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 17.23/17.46      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 17.23/17.46  thf('46', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('clc', [status(thm)], ['34', '45'])).
% 17.23/17.46  thf('47', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(cc2_relset_1, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.23/17.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 17.23/17.46  thf('48', plain,
% 17.23/17.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.23/17.46         ((v5_relat_1 @ X15 @ X17)
% 17.23/17.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 17.23/17.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 17.23/17.46  thf('49', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 17.23/17.46      inference('sup-', [status(thm)], ['47', '48'])).
% 17.23/17.46  thf('50', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(t2_subset, axiom,
% 17.23/17.46    (![A:$i,B:$i]:
% 17.23/17.46     ( ( m1_subset_1 @ A @ B ) =>
% 17.23/17.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 17.23/17.46  thf('51', plain,
% 17.23/17.46      (![X3 : $i, X4 : $i]:
% 17.23/17.46         ((r2_hidden @ X3 @ X4)
% 17.23/17.46          | (v1_xboole_0 @ X4)
% 17.23/17.46          | ~ (m1_subset_1 @ X3 @ X4))),
% 17.23/17.46      inference('cnf', [status(esa)], [t2_subset])).
% 17.23/17.46  thf('52', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 17.23/17.46      inference('sup-', [status(thm)], ['50', '51'])).
% 17.23/17.46  thf('53', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ 
% 17.23/17.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_E))))),
% 17.23/17.46      inference('demod', [status(thm)], ['10', '13', '14', '31'])).
% 17.23/17.46  thf(t7_funct_2, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i,D:$i]:
% 17.23/17.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 17.23/17.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.23/17.46       ( ( r2_hidden @ C @ A ) =>
% 17.23/17.46         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 17.23/17.46           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 17.23/17.46  thf('54', plain,
% 17.23/17.46      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 17.23/17.46         (~ (r2_hidden @ X46 @ X47)
% 17.23/17.46          | ((X48) = (k1_xboole_0))
% 17.23/17.46          | ~ (v1_funct_1 @ X49)
% 17.23/17.46          | ~ (v1_funct_2 @ X49 @ X47 @ X48)
% 17.23/17.46          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 17.23/17.46          | (r2_hidden @ (k1_funct_1 @ X49 @ X46) @ X48))),
% 17.23/17.46      inference('cnf', [status(esa)], [t7_funct_2])).
% 17.23/17.46  thf('55', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k1_relat_1 @ sk_E))
% 17.23/17.46          | ~ (v1_funct_2 @ sk_D_2 @ sk_B_1 @ (k1_relat_1 @ sk_E))
% 17.23/17.46          | ~ (v1_funct_1 @ sk_D_2)
% 17.23/17.46          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 17.23/17.46          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 17.23/17.46      inference('sup-', [status(thm)], ['53', '54'])).
% 17.23/17.46  thf('56', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('demod', [status(thm)], ['4', '7'])).
% 17.23/17.46  thf('57', plain,
% 17.23/17.46      (![X44 : $i, X45 : $i]:
% 17.23/17.46         (~ (r1_tarski @ (k2_relat_1 @ X44) @ X45)
% 17.23/17.46          | (v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ X45)
% 17.23/17.46          | ~ (v1_funct_1 @ X44)
% 17.23/17.46          | ~ (v1_relat_1 @ X44))),
% 17.23/17.46      inference('cnf', [status(esa)], [t4_funct_2])).
% 17.23/17.46  thf('58', plain,
% 17.23/17.46      ((~ (v1_relat_1 @ sk_D_2)
% 17.23/17.46        | ~ (v1_funct_1 @ sk_D_2)
% 17.23/17.46        | (v1_funct_2 @ sk_D_2 @ (k1_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['56', '57'])).
% 17.23/17.46  thf('59', plain, ((v1_relat_1 @ sk_D_2)),
% 17.23/17.46      inference('sup-', [status(thm)], ['11', '12'])).
% 17.23/17.46  thf('60', plain, ((v1_funct_1 @ sk_D_2)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('61', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 17.23/17.46      inference('demod', [status(thm)], ['21', '30'])).
% 17.23/17.46  thf('62', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 17.23/17.46  thf('63', plain, ((v1_funct_1 @ sk_D_2)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('64', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k1_relat_1 @ sk_E))
% 17.23/17.46          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 17.23/17.46          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 17.23/17.46      inference('demod', [status(thm)], ['55', '62', '63'])).
% 17.23/17.46  thf('65', plain,
% 17.23/17.46      (((v1_xboole_0 @ sk_B_1)
% 17.23/17.46        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 17.23/17.46        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['52', '64'])).
% 17.23/17.46  thf('66', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]:
% 17.23/17.46         (~ (v1_xboole_0 @ X1)
% 17.23/17.46          | ((X0) = (k1_relat_1 @ X1))
% 17.23/17.46          | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('sup-', [status(thm)], ['38', '39'])).
% 17.23/17.46  thf('67', plain,
% 17.23/17.46      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('sup-', [status(thm)], ['35', '40'])).
% 17.23/17.46  thf('68', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]:
% 17.23/17.46         (((k1_xboole_0) = (X0))
% 17.23/17.46          | ~ (v1_xboole_0 @ X0)
% 17.23/17.46          | ~ (v1_xboole_0 @ X1)
% 17.23/17.46          | ~ (v1_xboole_0 @ X1))),
% 17.23/17.46      inference('sup+', [status(thm)], ['66', '67'])).
% 17.23/17.46  thf('69', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]:
% 17.23/17.46         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 17.23/17.46      inference('simplify', [status(thm)], ['68'])).
% 17.23/17.46  thf('70', plain,
% 17.23/17.46      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('condensation', [status(thm)], ['69'])).
% 17.23/17.46  thf('71', plain,
% 17.23/17.46      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('condensation', [status(thm)], ['69'])).
% 17.23/17.46  thf('72', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i]:
% 17.23/17.46         (((X0) = (X1)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 17.23/17.46      inference('sup+', [status(thm)], ['70', '71'])).
% 17.23/17.46  thf('73', plain, (((sk_B_1) != (k1_xboole_0))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('74', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         (((X0) != (k1_xboole_0))
% 17.23/17.46          | ~ (v1_xboole_0 @ sk_B_1)
% 17.23/17.46          | ~ (v1_xboole_0 @ X0))),
% 17.23/17.46      inference('sup-', [status(thm)], ['72', '73'])).
% 17.23/17.46  thf('75', plain,
% 17.23/17.46      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 17.23/17.46      inference('simplify', [status(thm)], ['74'])).
% 17.23/17.46  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.23/17.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.23/17.46  thf('77', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 17.23/17.46      inference('simplify_reflect+', [status(thm)], ['75', '76'])).
% 17.23/17.46  thf('78', plain,
% 17.23/17.46      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))
% 17.23/17.46        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 17.23/17.46      inference('clc', [status(thm)], ['65', '77'])).
% 17.23/17.46  thf(d8_partfun1, axiom,
% 17.23/17.46    (![A:$i,B:$i]:
% 17.23/17.46     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 17.23/17.46       ( ![C:$i]:
% 17.23/17.46         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 17.23/17.46           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 17.23/17.46  thf('79', plain,
% 17.23/17.46      (![X35 : $i, X36 : $i, X37 : $i]:
% 17.23/17.46         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 17.23/17.46          | ((k7_partfun1 @ X37 @ X36 @ X35) = (k1_funct_1 @ X36 @ X35))
% 17.23/17.46          | ~ (v1_funct_1 @ X36)
% 17.23/17.46          | ~ (v5_relat_1 @ X36 @ X37)
% 17.23/17.46          | ~ (v1_relat_1 @ X36))),
% 17.23/17.46      inference('cnf', [status(esa)], [d8_partfun1])).
% 17.23/17.46  thf('80', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 17.23/17.46          | ~ (v1_relat_1 @ sk_E)
% 17.23/17.46          | ~ (v5_relat_1 @ sk_E @ X0)
% 17.23/17.46          | ~ (v1_funct_1 @ sk_E)
% 17.23/17.46          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 17.23/17.46              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 17.23/17.46      inference('sup-', [status(thm)], ['78', '79'])).
% 17.23/17.46  thf('81', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('82', plain,
% 17.23/17.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 17.23/17.46         ((v1_relat_1 @ X12)
% 17.23/17.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 17.23/17.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.23/17.46  thf('83', plain, ((v1_relat_1 @ sk_E)),
% 17.23/17.46      inference('sup-', [status(thm)], ['81', '82'])).
% 17.23/17.46  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('85', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 17.23/17.46          | ~ (v5_relat_1 @ sk_E @ X0)
% 17.23/17.46          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 17.23/17.46              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 17.23/17.46      inference('demod', [status(thm)], ['80', '83', '84'])).
% 17.23/17.46  thf('86', plain,
% 17.23/17.46      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 17.23/17.46          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))
% 17.23/17.46        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['49', '85'])).
% 17.23/17.46  thf('87', plain,
% 17.23/17.46      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E) @ 
% 17.23/17.46         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('88', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('89', plain,
% 17.23/17.46      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('sup-', [status(thm)], ['1', '2'])).
% 17.23/17.46  thf('90', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf(t185_funct_2, axiom,
% 17.23/17.46    (![A:$i,B:$i,C:$i]:
% 17.23/17.46     ( ( ~( v1_xboole_0 @ C ) ) =>
% 17.23/17.46       ( ![D:$i]:
% 17.23/17.46         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 17.23/17.46             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 17.23/17.46           ( ![E:$i]:
% 17.23/17.46             ( ( ( v1_funct_1 @ E ) & 
% 17.23/17.46                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 17.23/17.46               ( ![F:$i]:
% 17.23/17.46                 ( ( m1_subset_1 @ F @ B ) =>
% 17.23/17.46                   ( ( r1_tarski @
% 17.23/17.46                       ( k2_relset_1 @ B @ C @ D ) @ 
% 17.23/17.46                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 17.23/17.46                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 17.23/17.46                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 17.23/17.46                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 17.23/17.46  thf('91', plain,
% 17.23/17.46      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 17.23/17.46         (~ (v1_funct_1 @ X38)
% 17.23/17.46          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 17.23/17.46          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 17.23/17.46          | ~ (m1_subset_1 @ X41 @ X39)
% 17.23/17.46          | ((k1_funct_1 @ (k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42) @ X41)
% 17.23/17.46              = (k1_funct_1 @ X42 @ (k1_funct_1 @ X38 @ X41)))
% 17.23/17.46          | ((X39) = (k1_xboole_0))
% 17.23/17.46          | ~ (r1_tarski @ (k2_relset_1 @ X39 @ X40 @ X38) @ 
% 17.23/17.46               (k1_relset_1 @ X40 @ X43 @ X42))
% 17.23/17.46          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X43)))
% 17.23/17.46          | ~ (v1_funct_1 @ X42)
% 17.23/17.46          | (v1_xboole_0 @ X40))),
% 17.23/17.46      inference('cnf', [status(esa)], [t185_funct_2])).
% 17.23/17.46  thf('92', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.23/17.46         ((v1_xboole_0 @ sk_C_1)
% 17.23/17.46          | ~ (v1_funct_1 @ X0)
% 17.23/17.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 17.23/17.46          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) @ 
% 17.23/17.46               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 17.23/17.46          | ((sk_B_1) = (k1_xboole_0))
% 17.23/17.46          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D_2 @ X0) @ 
% 17.23/17.46              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 17.23/17.46          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 17.23/17.46          | ~ (v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1)
% 17.23/17.46          | ~ (v1_funct_1 @ sk_D_2))),
% 17.23/17.46      inference('sup-', [status(thm)], ['90', '91'])).
% 17.23/17.46  thf('93', plain,
% 17.23/17.46      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 17.23/17.46      inference('sup-', [status(thm)], ['5', '6'])).
% 17.23/17.46  thf('94', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_1)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('95', plain, ((v1_funct_1 @ sk_D_2)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('96', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.23/17.46         ((v1_xboole_0 @ sk_C_1)
% 17.23/17.46          | ~ (v1_funct_1 @ X0)
% 17.23/17.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 17.23/17.46          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 17.23/17.46               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 17.23/17.46          | ((sk_B_1) = (k1_xboole_0))
% 17.23/17.46          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D_2 @ X0) @ 
% 17.23/17.46              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 17.23/17.46          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 17.23/17.46      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 17.23/17.46  thf('97', plain, (((sk_B_1) != (k1_xboole_0))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('98', plain,
% 17.23/17.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.23/17.46         ((v1_xboole_0 @ sk_C_1)
% 17.23/17.46          | ~ (v1_funct_1 @ X0)
% 17.23/17.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 17.23/17.46          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 17.23/17.46               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 17.23/17.46          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D_2 @ X0) @ 
% 17.23/17.46              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 17.23/17.46          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 17.23/17.46      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 17.23/17.46  thf('99', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 17.23/17.46          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 17.23/17.46          | ((k1_funct_1 @ 
% 17.23/17.46              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 17.23/17.46              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 17.23/17.46          | ~ (m1_subset_1 @ sk_E @ 
% 17.23/17.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 17.23/17.46          | ~ (v1_funct_1 @ sk_E)
% 17.23/17.46          | (v1_xboole_0 @ sk_C_1))),
% 17.23/17.46      inference('sup-', [status(thm)], ['89', '98'])).
% 17.23/17.46  thf('100', plain,
% 17.23/17.46      ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 17.23/17.46      inference('demod', [status(thm)], ['4', '7'])).
% 17.23/17.46  thf('101', plain,
% 17.23/17.46      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('102', plain, ((v1_funct_1 @ sk_E)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('103', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 17.23/17.46          | ((k1_funct_1 @ 
% 17.23/17.46              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 17.23/17.46              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 17.23/17.46          | (v1_xboole_0 @ sk_C_1))),
% 17.23/17.46      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 17.23/17.46  thf('104', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 17.23/17.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.23/17.46  thf('105', plain,
% 17.23/17.46      (![X0 : $i]:
% 17.23/17.46         (((k1_funct_1 @ 
% 17.23/17.46            (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 17.23/17.46            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 17.23/17.46          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 17.23/17.46      inference('clc', [status(thm)], ['103', '104'])).
% 17.23/17.46  thf('106', plain,
% 17.23/17.46      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_E) @ 
% 17.23/17.46         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['88', '105'])).
% 17.23/17.46  thf('107', plain,
% 17.23/17.46      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 17.23/17.46         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 17.23/17.46      inference('demod', [status(thm)], ['87', '106'])).
% 17.23/17.46  thf('108', plain,
% 17.23/17.46      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 17.23/17.46          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))
% 17.23/17.46        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 17.23/17.46      inference('sup-', [status(thm)], ['86', '107'])).
% 17.23/17.46  thf('109', plain, (((k1_relat_1 @ sk_E) = (k1_xboole_0))),
% 17.23/17.46      inference('simplify', [status(thm)], ['108'])).
% 17.23/17.46  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.23/17.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.23/17.46  thf('111', plain, ($false),
% 17.23/17.46      inference('demod', [status(thm)], ['46', '109', '110'])).
% 17.23/17.46  
% 17.23/17.46  % SZS output end Refutation
% 17.23/17.46  
% 17.23/17.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
