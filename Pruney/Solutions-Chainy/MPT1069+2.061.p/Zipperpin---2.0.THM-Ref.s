%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h4emqlyXBj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:09 EST 2020

% Result     : Theorem 15.82s
% Output     : Refutation 15.82s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 222 expanded)
%              Number of leaves         :   49 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          : 1229 (4221 expanded)
%              Number of equality atoms :   64 ( 182 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
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

thf('5',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X47 @ X45 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X45 @ X46 @ X49 @ X44 @ X48 ) @ X47 )
        = ( k1_funct_1 @ X48 @ ( k1_funct_1 @ X44 @ X47 ) ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X45 @ X46 @ X44 ) @ ( k1_relset_1 @ X46 @ X49 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference(clc,[status(thm)],['33','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2 ),
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

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
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

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('58',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['53','64'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('67',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['68','69','74'])).

thf('76',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['46','75'])).

thf('77',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('85',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ ( k1_relat_1 @ X42 ) )
      | ( ( k7_partfun1 @ X43 @ X42 @ X41 )
        = ( k1_funct_1 @ X42 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v5_relat_1 @ X42 @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['86','91','92'])).

thf('94',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','93'])).

thf('95',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','94'])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h4emqlyXBj
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 15.82/16.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.82/16.02  % Solved by: fo/fo7.sh
% 15.82/16.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.82/16.02  % done 13264 iterations in 15.546s
% 15.82/16.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.82/16.02  % SZS output start Refutation
% 15.82/16.02  thf(sk_A_type, type, sk_A: $i).
% 15.82/16.02  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.82/16.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.82/16.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.82/16.02  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.82/16.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.82/16.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.82/16.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.82/16.02  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 15.82/16.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 15.82/16.02  thf(sk_C_2_type, type, sk_C_2: $i).
% 15.82/16.02  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 15.82/16.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.82/16.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.82/16.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 15.82/16.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.82/16.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.82/16.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.82/16.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.82/16.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.82/16.02  thf(sk_F_type, type, sk_F: $i).
% 15.82/16.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.82/16.02  thf(sk_B_type, type, sk_B: $i > $i).
% 15.82/16.02  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 15.82/16.02  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 15.82/16.02  thf(sk_E_type, type, sk_E: $i).
% 15.82/16.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.82/16.02  thf(sk_D_2_type, type, sk_D_2: $i).
% 15.82/16.02  thf(t186_funct_2, conjecture,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( ~( v1_xboole_0 @ C ) ) =>
% 15.82/16.02       ( ![D:$i]:
% 15.82/16.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 15.82/16.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.82/16.02           ( ![E:$i]:
% 15.82/16.02             ( ( ( v1_funct_1 @ E ) & 
% 15.82/16.02                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 15.82/16.02               ( ![F:$i]:
% 15.82/16.02                 ( ( m1_subset_1 @ F @ B ) =>
% 15.82/16.02                   ( ( r1_tarski @
% 15.82/16.02                       ( k2_relset_1 @ B @ C @ D ) @ 
% 15.82/16.02                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 15.82/16.02                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 15.82/16.02                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 15.82/16.02                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 15.82/16.02  thf(zf_stmt_0, negated_conjecture,
% 15.82/16.02    (~( ![A:$i,B:$i,C:$i]:
% 15.82/16.02        ( ( ~( v1_xboole_0 @ C ) ) =>
% 15.82/16.02          ( ![D:$i]:
% 15.82/16.02            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 15.82/16.02                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.82/16.02              ( ![E:$i]:
% 15.82/16.02                ( ( ( v1_funct_1 @ E ) & 
% 15.82/16.02                    ( m1_subset_1 @
% 15.82/16.02                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 15.82/16.02                  ( ![F:$i]:
% 15.82/16.02                    ( ( m1_subset_1 @ F @ B ) =>
% 15.82/16.02                      ( ( r1_tarski @
% 15.82/16.02                          ( k2_relset_1 @ B @ C @ D ) @ 
% 15.82/16.02                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 15.82/16.02                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 15.82/16.02                          ( ( k1_funct_1 @
% 15.82/16.02                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 15.82/16.02                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 15.82/16.02    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 15.82/16.02  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('1', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(redefinition_k1_relset_1, axiom,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.82/16.02       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.82/16.02  thf('2', plain,
% 15.82/16.02      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.82/16.02         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 15.82/16.02          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 15.82/16.02      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.82/16.02  thf('3', plain,
% 15.82/16.02      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.82/16.02      inference('sup-', [status(thm)], ['1', '2'])).
% 15.82/16.02  thf('4', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(t185_funct_2, axiom,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( ~( v1_xboole_0 @ C ) ) =>
% 15.82/16.02       ( ![D:$i]:
% 15.82/16.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 15.82/16.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.82/16.02           ( ![E:$i]:
% 15.82/16.02             ( ( ( v1_funct_1 @ E ) & 
% 15.82/16.02                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 15.82/16.02               ( ![F:$i]:
% 15.82/16.02                 ( ( m1_subset_1 @ F @ B ) =>
% 15.82/16.02                   ( ( r1_tarski @
% 15.82/16.02                       ( k2_relset_1 @ B @ C @ D ) @ 
% 15.82/16.02                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 15.82/16.02                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 15.82/16.02                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 15.82/16.02                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 15.82/16.02  thf('5', plain,
% 15.82/16.02      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 15.82/16.02         (~ (v1_funct_1 @ X44)
% 15.82/16.02          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 15.82/16.02          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 15.82/16.02          | ~ (m1_subset_1 @ X47 @ X45)
% 15.82/16.02          | ((k1_funct_1 @ (k8_funct_2 @ X45 @ X46 @ X49 @ X44 @ X48) @ X47)
% 15.82/16.02              = (k1_funct_1 @ X48 @ (k1_funct_1 @ X44 @ X47)))
% 15.82/16.02          | ((X45) = (k1_xboole_0))
% 15.82/16.02          | ~ (r1_tarski @ (k2_relset_1 @ X45 @ X46 @ X44) @ 
% 15.82/16.02               (k1_relset_1 @ X46 @ X49 @ X48))
% 15.82/16.02          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X49)))
% 15.82/16.02          | ~ (v1_funct_1 @ X48)
% 15.82/16.02          | (v1_xboole_0 @ X46))),
% 15.82/16.02      inference('cnf', [status(esa)], [t185_funct_2])).
% 15.82/16.02  thf('6', plain,
% 15.82/16.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.82/16.02         ((v1_xboole_0 @ sk_C_2)
% 15.82/16.02          | ~ (v1_funct_1 @ X0)
% 15.82/16.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 15.82/16.02          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.82/16.02               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 15.82/16.02          | ((sk_B_1) = (k1_xboole_0))
% 15.82/16.02          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ 
% 15.82/16.02              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 15.82/16.02          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 15.82/16.02          | ~ (v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)
% 15.82/16.02          | ~ (v1_funct_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['4', '5'])).
% 15.82/16.02  thf('7', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(redefinition_k2_relset_1, axiom,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.82/16.02       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 15.82/16.02  thf('8', plain,
% 15.82/16.02      (![X30 : $i, X31 : $i, X32 : $i]:
% 15.82/16.02         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 15.82/16.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 15.82/16.02      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 15.82/16.02  thf('9', plain,
% 15.82/16.02      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['7', '8'])).
% 15.82/16.02  thf('10', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('11', plain, ((v1_funct_1 @ sk_D_2)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('12', plain,
% 15.82/16.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.82/16.02         ((v1_xboole_0 @ sk_C_2)
% 15.82/16.02          | ~ (v1_funct_1 @ X0)
% 15.82/16.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 15.82/16.02          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 15.82/16.02               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 15.82/16.02          | ((sk_B_1) = (k1_xboole_0))
% 15.82/16.02          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ 
% 15.82/16.02              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 15.82/16.02          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 15.82/16.02      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 15.82/16.02  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('14', plain,
% 15.82/16.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.82/16.02         ((v1_xboole_0 @ sk_C_2)
% 15.82/16.02          | ~ (v1_funct_1 @ X0)
% 15.82/16.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 15.82/16.02          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 15.82/16.02               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 15.82/16.02          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ 
% 15.82/16.02              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 15.82/16.02          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 15.82/16.02      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 15.82/16.02  thf('15', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 15.82/16.02          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 15.82/16.02          | ((k1_funct_1 @ 
% 15.82/16.02              (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 15.82/16.02              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 15.82/16.02          | ~ (m1_subset_1 @ sk_E @ 
% 15.82/16.02               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 15.82/16.02          | ~ (v1_funct_1 @ sk_E)
% 15.82/16.02          | (v1_xboole_0 @ sk_C_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['3', '14'])).
% 15.82/16.02  thf('16', plain,
% 15.82/16.02      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.82/16.02        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('17', plain,
% 15.82/16.02      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.82/16.02      inference('sup-', [status(thm)], ['1', '2'])).
% 15.82/16.02  thf('18', plain,
% 15.82/16.02      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.82/16.02        (k1_relat_1 @ sk_E))),
% 15.82/16.02      inference('demod', [status(thm)], ['16', '17'])).
% 15.82/16.02  thf('19', plain,
% 15.82/16.02      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['7', '8'])).
% 15.82/16.02  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 15.82/16.02      inference('demod', [status(thm)], ['18', '19'])).
% 15.82/16.02  thf('21', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('23', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 15.82/16.02          | ((k1_funct_1 @ 
% 15.82/16.02              (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 15.82/16.02              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 15.82/16.02          | (v1_xboole_0 @ sk_C_2))),
% 15.82/16.02      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 15.82/16.02  thf('24', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('25', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (((k1_funct_1 @ 
% 15.82/16.02            (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 15.82/16.02            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 15.82/16.02          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 15.82/16.02      inference('clc', [status(thm)], ['23', '24'])).
% 15.82/16.02  thf('26', plain,
% 15.82/16.02      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 15.82/16.02         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.82/16.02      inference('sup-', [status(thm)], ['0', '25'])).
% 15.82/16.02  thf('27', plain,
% 15.82/16.02      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 15.82/16.02         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('28', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(cc2_relset_1, axiom,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.82/16.02       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.82/16.02  thf('29', plain,
% 15.82/16.02      (![X24 : $i, X25 : $i, X26 : $i]:
% 15.82/16.02         ((v5_relat_1 @ X24 @ X26)
% 15.82/16.02          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 15.82/16.02      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.82/16.02  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 15.82/16.02      inference('sup-', [status(thm)], ['28', '29'])).
% 15.82/16.02  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(t2_subset, axiom,
% 15.82/16.02    (![A:$i,B:$i]:
% 15.82/16.02     ( ( m1_subset_1 @ A @ B ) =>
% 15.82/16.02       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 15.82/16.02  thf('32', plain,
% 15.82/16.02      (![X9 : $i, X10 : $i]:
% 15.82/16.02         ((r2_hidden @ X9 @ X10)
% 15.82/16.02          | (v1_xboole_0 @ X10)
% 15.82/16.02          | ~ (m1_subset_1 @ X9 @ X10))),
% 15.82/16.02      inference('cnf', [status(esa)], [t2_subset])).
% 15.82/16.02  thf('33', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 15.82/16.02      inference('sup-', [status(thm)], ['31', '32'])).
% 15.82/16.02  thf(l13_xboole_0, axiom,
% 15.82/16.02    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 15.82/16.02  thf('34', plain,
% 15.82/16.02      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 15.82/16.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.82/16.02  thf('35', plain,
% 15.82/16.02      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 15.82/16.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.82/16.02  thf('36', plain,
% 15.82/16.02      (![X0 : $i, X1 : $i]:
% 15.82/16.02         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 15.82/16.02      inference('sup+', [status(thm)], ['34', '35'])).
% 15.82/16.02  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('38', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (((X0) != (k1_xboole_0))
% 15.82/16.02          | ~ (v1_xboole_0 @ X0)
% 15.82/16.02          | ~ (v1_xboole_0 @ sk_B_1))),
% 15.82/16.02      inference('sup-', [status(thm)], ['36', '37'])).
% 15.82/16.02  thf('39', plain,
% 15.82/16.02      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 15.82/16.02      inference('simplify', [status(thm)], ['38'])).
% 15.82/16.02  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.82/16.02  thf('40', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 15.82/16.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.82/16.02  thf(d1_xboole_0, axiom,
% 15.82/16.02    (![A:$i]:
% 15.82/16.02     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 15.82/16.02  thf('41', plain,
% 15.82/16.02      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 15.82/16.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 15.82/16.02  thf(t7_ordinal1, axiom,
% 15.82/16.02    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.82/16.02  thf('42', plain,
% 15.82/16.02      (![X22 : $i, X23 : $i]:
% 15.82/16.02         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 15.82/16.02      inference('cnf', [status(esa)], [t7_ordinal1])).
% 15.82/16.02  thf('43', plain,
% 15.82/16.02      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 15.82/16.02      inference('sup-', [status(thm)], ['41', '42'])).
% 15.82/16.02  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 15.82/16.02      inference('sup-', [status(thm)], ['40', '43'])).
% 15.82/16.02  thf('45', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 15.82/16.02      inference('demod', [status(thm)], ['39', '44'])).
% 15.82/16.02  thf('46', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 15.82/16.02      inference('clc', [status(thm)], ['33', '45'])).
% 15.82/16.02  thf('47', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(d1_funct_2, axiom,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.82/16.02       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.82/16.02           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.82/16.02             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.82/16.02         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.82/16.02           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.82/16.02             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.82/16.02  thf(zf_stmt_1, axiom,
% 15.82/16.02    (![C:$i,B:$i,A:$i]:
% 15.82/16.02     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.82/16.02       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.82/16.02  thf('48', plain,
% 15.82/16.02      (![X35 : $i, X36 : $i, X37 : $i]:
% 15.82/16.02         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 15.82/16.02          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 15.82/16.02          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.82/16.02  thf('49', plain,
% 15.82/16.02      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 15.82/16.02        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 15.82/16.02      inference('sup-', [status(thm)], ['47', '48'])).
% 15.82/16.02  thf('50', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('51', plain,
% 15.82/16.02      (![X27 : $i, X28 : $i, X29 : $i]:
% 15.82/16.02         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 15.82/16.02          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 15.82/16.02      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.82/16.02  thf('52', plain,
% 15.82/16.02      (((k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['50', '51'])).
% 15.82/16.02  thf('53', plain,
% 15.82/16.02      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 15.82/16.02        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 15.82/16.02      inference('demod', [status(thm)], ['49', '52'])).
% 15.82/16.02  thf('54', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.82/16.02  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 15.82/16.02  thf(zf_stmt_4, axiom,
% 15.82/16.02    (![B:$i,A:$i]:
% 15.82/16.02     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.82/16.02       ( zip_tseitin_0 @ B @ A ) ))).
% 15.82/16.02  thf(zf_stmt_5, axiom,
% 15.82/16.02    (![A:$i,B:$i,C:$i]:
% 15.82/16.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.82/16.02       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.82/16.02         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.82/16.02           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.82/16.02             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.82/16.02  thf('55', plain,
% 15.82/16.02      (![X38 : $i, X39 : $i, X40 : $i]:
% 15.82/16.02         (~ (zip_tseitin_0 @ X38 @ X39)
% 15.82/16.02          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 15.82/16.02          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.82/16.02  thf('56', plain,
% 15.82/16.02      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 15.82/16.02        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B_1))),
% 15.82/16.02      inference('sup-', [status(thm)], ['54', '55'])).
% 15.82/16.02  thf('57', plain,
% 15.82/16.02      (![X33 : $i, X34 : $i]:
% 15.82/16.02         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_4])).
% 15.82/16.02  thf('58', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 15.82/16.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.82/16.02  thf('59', plain,
% 15.82/16.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.82/16.02         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 15.82/16.02      inference('sup+', [status(thm)], ['57', '58'])).
% 15.82/16.02  thf('60', plain,
% 15.82/16.02      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 15.82/16.02      inference('sup-', [status(thm)], ['41', '42'])).
% 15.82/16.02  thf('61', plain,
% 15.82/16.02      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 15.82/16.02      inference('sup-', [status(thm)], ['59', '60'])).
% 15.82/16.02  thf('62', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('63', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_2 @ X0)),
% 15.82/16.02      inference('sup-', [status(thm)], ['61', '62'])).
% 15.82/16.02  thf('64', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)),
% 15.82/16.02      inference('demod', [status(thm)], ['56', '63'])).
% 15.82/16.02  thf('65', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('demod', [status(thm)], ['53', '64'])).
% 15.82/16.02  thf(d5_funct_1, axiom,
% 15.82/16.02    (![A:$i]:
% 15.82/16.02     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.82/16.02       ( ![B:$i]:
% 15.82/16.02         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 15.82/16.02           ( ![C:$i]:
% 15.82/16.02             ( ( r2_hidden @ C @ B ) <=>
% 15.82/16.02               ( ?[D:$i]:
% 15.82/16.02                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 15.82/16.02                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 15.82/16.02  thf('66', plain,
% 15.82/16.02      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 15.82/16.02         (((X18) != (k2_relat_1 @ X16))
% 15.82/16.02          | (r2_hidden @ X20 @ X18)
% 15.82/16.02          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 15.82/16.02          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 15.82/16.02          | ~ (v1_funct_1 @ X16)
% 15.82/16.02          | ~ (v1_relat_1 @ X16))),
% 15.82/16.02      inference('cnf', [status(esa)], [d5_funct_1])).
% 15.82/16.02  thf('67', plain,
% 15.82/16.02      (![X16 : $i, X21 : $i]:
% 15.82/16.02         (~ (v1_relat_1 @ X16)
% 15.82/16.02          | ~ (v1_funct_1 @ X16)
% 15.82/16.02          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 15.82/16.02          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 15.82/16.02      inference('simplify', [status(thm)], ['66'])).
% 15.82/16.02  thf('68', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (~ (r2_hidden @ X0 @ sk_B_1)
% 15.82/16.02          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 15.82/16.02          | ~ (v1_funct_1 @ sk_D_2)
% 15.82/16.02          | ~ (v1_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['65', '67'])).
% 15.82/16.02  thf('69', plain, ((v1_funct_1 @ sk_D_2)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('70', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(cc2_relat_1, axiom,
% 15.82/16.02    (![A:$i]:
% 15.82/16.02     ( ( v1_relat_1 @ A ) =>
% 15.82/16.02       ( ![B:$i]:
% 15.82/16.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 15.82/16.02  thf('71', plain,
% 15.82/16.02      (![X11 : $i, X12 : $i]:
% 15.82/16.02         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 15.82/16.02          | (v1_relat_1 @ X11)
% 15.82/16.02          | ~ (v1_relat_1 @ X12))),
% 15.82/16.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 15.82/16.02  thf('72', plain,
% 15.82/16.02      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2))
% 15.82/16.02        | (v1_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['70', '71'])).
% 15.82/16.02  thf(fc6_relat_1, axiom,
% 15.82/16.02    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 15.82/16.02  thf('73', plain,
% 15.82/16.02      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 15.82/16.02      inference('cnf', [status(esa)], [fc6_relat_1])).
% 15.82/16.02  thf('74', plain, ((v1_relat_1 @ sk_D_2)),
% 15.82/16.02      inference('demod', [status(thm)], ['72', '73'])).
% 15.82/16.02  thf('75', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (~ (r2_hidden @ X0 @ sk_B_1)
% 15.82/16.02          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 15.82/16.02      inference('demod', [status(thm)], ['68', '69', '74'])).
% 15.82/16.02  thf('76', plain,
% 15.82/16.02      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k2_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['46', '75'])).
% 15.82/16.02  thf('77', plain,
% 15.82/16.02      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.82/16.02        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf(d3_tarski, axiom,
% 15.82/16.02    (![A:$i,B:$i]:
% 15.82/16.02     ( ( r1_tarski @ A @ B ) <=>
% 15.82/16.02       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 15.82/16.02  thf('78', plain,
% 15.82/16.02      (![X3 : $i, X4 : $i, X5 : $i]:
% 15.82/16.02         (~ (r2_hidden @ X3 @ X4)
% 15.82/16.02          | (r2_hidden @ X3 @ X5)
% 15.82/16.02          | ~ (r1_tarski @ X4 @ X5))),
% 15.82/16.02      inference('cnf', [status(esa)], [d3_tarski])).
% 15.82/16.02  thf('79', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 15.82/16.02          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 15.82/16.02      inference('sup-', [status(thm)], ['77', '78'])).
% 15.82/16.02  thf('80', plain,
% 15.82/16.02      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.82/16.02      inference('sup-', [status(thm)], ['1', '2'])).
% 15.82/16.02  thf('81', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 15.82/16.02          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 15.82/16.02      inference('demod', [status(thm)], ['79', '80'])).
% 15.82/16.02  thf('82', plain,
% 15.82/16.02      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 15.82/16.02      inference('sup-', [status(thm)], ['7', '8'])).
% 15.82/16.02  thf('83', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 15.82/16.02          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 15.82/16.02      inference('demod', [status(thm)], ['81', '82'])).
% 15.82/16.02  thf('84', plain,
% 15.82/16.02      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 15.82/16.02      inference('sup-', [status(thm)], ['76', '83'])).
% 15.82/16.02  thf(d8_partfun1, axiom,
% 15.82/16.02    (![A:$i,B:$i]:
% 15.82/16.02     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 15.82/16.02       ( ![C:$i]:
% 15.82/16.02         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 15.82/16.02           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 15.82/16.02  thf('85', plain,
% 15.82/16.02      (![X41 : $i, X42 : $i, X43 : $i]:
% 15.82/16.02         (~ (r2_hidden @ X41 @ (k1_relat_1 @ X42))
% 15.82/16.02          | ((k7_partfun1 @ X43 @ X42 @ X41) = (k1_funct_1 @ X42 @ X41))
% 15.82/16.02          | ~ (v1_funct_1 @ X42)
% 15.82/16.02          | ~ (v5_relat_1 @ X42 @ X43)
% 15.82/16.02          | ~ (v1_relat_1 @ X42))),
% 15.82/16.02      inference('cnf', [status(esa)], [d8_partfun1])).
% 15.82/16.02  thf('86', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (~ (v1_relat_1 @ sk_E)
% 15.82/16.02          | ~ (v5_relat_1 @ sk_E @ X0)
% 15.82/16.02          | ~ (v1_funct_1 @ sk_E)
% 15.82/16.02          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 15.82/16.02              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 15.82/16.02      inference('sup-', [status(thm)], ['84', '85'])).
% 15.82/16.02  thf('87', plain,
% 15.82/16.02      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('88', plain,
% 15.82/16.02      (![X11 : $i, X12 : $i]:
% 15.82/16.02         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 15.82/16.02          | (v1_relat_1 @ X11)
% 15.82/16.02          | ~ (v1_relat_1 @ X12))),
% 15.82/16.02      inference('cnf', [status(esa)], [cc2_relat_1])).
% 15.82/16.02  thf('89', plain,
% 15.82/16.02      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 15.82/16.02      inference('sup-', [status(thm)], ['87', '88'])).
% 15.82/16.02  thf('90', plain,
% 15.82/16.02      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 15.82/16.02      inference('cnf', [status(esa)], [fc6_relat_1])).
% 15.82/16.02  thf('91', plain, ((v1_relat_1 @ sk_E)),
% 15.82/16.02      inference('demod', [status(thm)], ['89', '90'])).
% 15.82/16.02  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 15.82/16.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.82/16.02  thf('93', plain,
% 15.82/16.02      (![X0 : $i]:
% 15.82/16.02         (~ (v5_relat_1 @ sk_E @ X0)
% 15.82/16.02          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 15.82/16.02              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 15.82/16.02      inference('demod', [status(thm)], ['86', '91', '92'])).
% 15.82/16.02  thf('94', plain,
% 15.82/16.02      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 15.82/16.02         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.82/16.02      inference('sup-', [status(thm)], ['30', '93'])).
% 15.82/16.02  thf('95', plain,
% 15.82/16.02      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 15.82/16.02         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.82/16.02      inference('demod', [status(thm)], ['27', '94'])).
% 15.82/16.02  thf('96', plain, ($false),
% 15.82/16.02      inference('simplify_reflect-', [status(thm)], ['26', '95'])).
% 15.82/16.02  
% 15.82/16.02  % SZS output end Refutation
% 15.82/16.02  
% 15.82/16.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
