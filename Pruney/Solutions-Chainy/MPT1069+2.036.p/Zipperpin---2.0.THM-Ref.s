%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y3thkhC4To

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:06 EST 2020

% Result     : Theorem 15.79s
% Output     : Refutation 15.79s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 216 expanded)
%              Number of leaves         :   48 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          : 1205 (4193 expanded)
%              Number of equality atoms :   64 ( 182 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X44 @ X45 @ X48 @ X43 @ X47 ) @ X46 )
        = ( k1_funct_1 @ X47 @ ( k1_funct_1 @ X43 @ X46 ) ) )
      | ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X44 @ X45 @ X43 ) @ ( k1_relset_1 @ X45 @ X48 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ( v1_xboole_0 @ X45 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
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
    ! [X12: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( X16
       != ( k1_funct_1 @ X12 @ X17 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('67',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('74',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['46','73'])).

thf('75',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('76',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('83',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ X41 ) )
      | ( ( k7_partfun1 @ X42 @ X41 @ X40 )
        = ( k1_funct_1 @ X41 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v5_relat_1 @ X41 @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['84','87','88'])).

thf('90',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','89'])).

thf('91',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y3thkhC4To
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.79/16.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.79/16.00  % Solved by: fo/fo7.sh
% 15.79/16.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.79/16.00  % done 13407 iterations in 15.540s
% 15.79/16.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.79/16.00  % SZS output start Refutation
% 15.79/16.00  thf(sk_D_2_type, type, sk_D_2: $i).
% 15.79/16.00  thf(sk_B_type, type, sk_B: $i > $i).
% 15.79/16.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 15.79/16.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 15.79/16.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.79/16.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 15.79/16.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.79/16.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 15.79/16.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 15.79/16.00  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 15.79/16.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 15.79/16.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 15.79/16.00  thf(sk_F_type, type, sk_F: $i).
% 15.79/16.00  thf(sk_C_2_type, type, sk_C_2: $i).
% 15.79/16.00  thf(sk_E_type, type, sk_E: $i).
% 15.79/16.00  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 15.79/16.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 15.79/16.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 15.79/16.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 15.79/16.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 15.79/16.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.79/16.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 15.79/16.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 15.79/16.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 15.79/16.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.79/16.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 15.79/16.00  thf(sk_A_type, type, sk_A: $i).
% 15.79/16.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 15.79/16.00  thf(t186_funct_2, conjecture,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( ~( v1_xboole_0 @ C ) ) =>
% 15.79/16.00       ( ![D:$i]:
% 15.79/16.00         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 15.79/16.00             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.79/16.00           ( ![E:$i]:
% 15.79/16.00             ( ( ( v1_funct_1 @ E ) & 
% 15.79/16.00                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 15.79/16.00               ( ![F:$i]:
% 15.79/16.00                 ( ( m1_subset_1 @ F @ B ) =>
% 15.79/16.00                   ( ( r1_tarski @
% 15.79/16.00                       ( k2_relset_1 @ B @ C @ D ) @ 
% 15.79/16.00                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 15.79/16.00                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 15.79/16.00                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 15.79/16.00                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 15.79/16.00  thf(zf_stmt_0, negated_conjecture,
% 15.79/16.00    (~( ![A:$i,B:$i,C:$i]:
% 15.79/16.00        ( ( ~( v1_xboole_0 @ C ) ) =>
% 15.79/16.00          ( ![D:$i]:
% 15.79/16.00            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 15.79/16.00                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.79/16.00              ( ![E:$i]:
% 15.79/16.00                ( ( ( v1_funct_1 @ E ) & 
% 15.79/16.00                    ( m1_subset_1 @
% 15.79/16.00                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 15.79/16.00                  ( ![F:$i]:
% 15.79/16.00                    ( ( m1_subset_1 @ F @ B ) =>
% 15.79/16.00                      ( ( r1_tarski @
% 15.79/16.00                          ( k2_relset_1 @ B @ C @ D ) @ 
% 15.79/16.00                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 15.79/16.00                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 15.79/16.00                          ( ( k1_funct_1 @
% 15.79/16.00                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 15.79/16.00                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 15.79/16.00    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 15.79/16.00  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('1', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(redefinition_k1_relset_1, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.79/16.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 15.79/16.00  thf('2', plain,
% 15.79/16.00      (![X26 : $i, X27 : $i, X28 : $i]:
% 15.79/16.00         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 15.79/16.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 15.79/16.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.79/16.00  thf('3', plain,
% 15.79/16.00      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.79/16.00      inference('sup-', [status(thm)], ['1', '2'])).
% 15.79/16.00  thf('4', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(t185_funct_2, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( ~( v1_xboole_0 @ C ) ) =>
% 15.79/16.00       ( ![D:$i]:
% 15.79/16.00         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 15.79/16.00             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 15.79/16.00           ( ![E:$i]:
% 15.79/16.00             ( ( ( v1_funct_1 @ E ) & 
% 15.79/16.00                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 15.79/16.00               ( ![F:$i]:
% 15.79/16.00                 ( ( m1_subset_1 @ F @ B ) =>
% 15.79/16.00                   ( ( r1_tarski @
% 15.79/16.00                       ( k2_relset_1 @ B @ C @ D ) @ 
% 15.79/16.00                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 15.79/16.00                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 15.79/16.00                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 15.79/16.00                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 15.79/16.00  thf('5', plain,
% 15.79/16.00      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 15.79/16.00         (~ (v1_funct_1 @ X43)
% 15.79/16.00          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 15.79/16.00          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 15.79/16.00          | ~ (m1_subset_1 @ X46 @ X44)
% 15.79/16.00          | ((k1_funct_1 @ (k8_funct_2 @ X44 @ X45 @ X48 @ X43 @ X47) @ X46)
% 15.79/16.00              = (k1_funct_1 @ X47 @ (k1_funct_1 @ X43 @ X46)))
% 15.79/16.00          | ((X44) = (k1_xboole_0))
% 15.79/16.00          | ~ (r1_tarski @ (k2_relset_1 @ X44 @ X45 @ X43) @ 
% 15.79/16.00               (k1_relset_1 @ X45 @ X48 @ X47))
% 15.79/16.00          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X48)))
% 15.79/16.00          | ~ (v1_funct_1 @ X47)
% 15.79/16.00          | (v1_xboole_0 @ X45))),
% 15.79/16.00      inference('cnf', [status(esa)], [t185_funct_2])).
% 15.79/16.00  thf('6', plain,
% 15.79/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.79/16.00         ((v1_xboole_0 @ sk_C_2)
% 15.79/16.00          | ~ (v1_funct_1 @ X0)
% 15.79/16.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 15.79/16.00          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.79/16.00               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 15.79/16.00          | ((sk_B_1) = (k1_xboole_0))
% 15.79/16.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ 
% 15.79/16.00              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 15.79/16.00          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 15.79/16.00          | ~ (v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)
% 15.79/16.00          | ~ (v1_funct_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['4', '5'])).
% 15.79/16.00  thf('7', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(redefinition_k2_relset_1, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.79/16.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 15.79/16.00  thf('8', plain,
% 15.79/16.00      (![X29 : $i, X30 : $i, X31 : $i]:
% 15.79/16.00         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 15.79/16.00          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 15.79/16.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 15.79/16.00  thf('9', plain,
% 15.79/16.00      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['7', '8'])).
% 15.79/16.00  thf('10', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('11', plain, ((v1_funct_1 @ sk_D_2)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('12', plain,
% 15.79/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.79/16.00         ((v1_xboole_0 @ sk_C_2)
% 15.79/16.00          | ~ (v1_funct_1 @ X0)
% 15.79/16.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 15.79/16.00          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 15.79/16.00               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 15.79/16.00          | ((sk_B_1) = (k1_xboole_0))
% 15.79/16.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ 
% 15.79/16.00              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 15.79/16.00          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 15.79/16.00      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 15.79/16.00  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('14', plain,
% 15.79/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.79/16.00         ((v1_xboole_0 @ sk_C_2)
% 15.79/16.00          | ~ (v1_funct_1 @ X0)
% 15.79/16.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 15.79/16.00          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 15.79/16.00               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 15.79/16.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ 
% 15.79/16.00              X2) = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 15.79/16.00          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 15.79/16.00      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 15.79/16.00  thf('15', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 15.79/16.00          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 15.79/16.00          | ((k1_funct_1 @ 
% 15.79/16.00              (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 15.79/16.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 15.79/16.00          | ~ (m1_subset_1 @ sk_E @ 
% 15.79/16.00               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 15.79/16.00          | ~ (v1_funct_1 @ sk_E)
% 15.79/16.00          | (v1_xboole_0 @ sk_C_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['3', '14'])).
% 15.79/16.00  thf('16', plain,
% 15.79/16.00      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.79/16.00        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('17', plain,
% 15.79/16.00      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.79/16.00      inference('sup-', [status(thm)], ['1', '2'])).
% 15.79/16.00  thf('18', plain,
% 15.79/16.00      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.79/16.00        (k1_relat_1 @ sk_E))),
% 15.79/16.00      inference('demod', [status(thm)], ['16', '17'])).
% 15.79/16.00  thf('19', plain,
% 15.79/16.00      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['7', '8'])).
% 15.79/16.00  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 15.79/16.00      inference('demod', [status(thm)], ['18', '19'])).
% 15.79/16.00  thf('21', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('23', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 15.79/16.00          | ((k1_funct_1 @ 
% 15.79/16.00              (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 15.79/16.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 15.79/16.00          | (v1_xboole_0 @ sk_C_2))),
% 15.79/16.00      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 15.79/16.00  thf('24', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('25', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (((k1_funct_1 @ 
% 15.79/16.00            (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 15.79/16.00            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 15.79/16.00          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 15.79/16.00      inference('clc', [status(thm)], ['23', '24'])).
% 15.79/16.00  thf('26', plain,
% 15.79/16.00      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 15.79/16.00         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.79/16.00      inference('sup-', [status(thm)], ['0', '25'])).
% 15.79/16.00  thf('27', plain,
% 15.79/16.00      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 15.79/16.00         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('28', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(cc2_relset_1, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.79/16.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 15.79/16.00  thf('29', plain,
% 15.79/16.00      (![X23 : $i, X24 : $i, X25 : $i]:
% 15.79/16.00         ((v5_relat_1 @ X23 @ X25)
% 15.79/16.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 15.79/16.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 15.79/16.00  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 15.79/16.00      inference('sup-', [status(thm)], ['28', '29'])).
% 15.79/16.00  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(t2_subset, axiom,
% 15.79/16.00    (![A:$i,B:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ A @ B ) =>
% 15.79/16.00       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 15.79/16.00  thf('32', plain,
% 15.79/16.00      (![X9 : $i, X10 : $i]:
% 15.79/16.00         ((r2_hidden @ X9 @ X10)
% 15.79/16.00          | (v1_xboole_0 @ X10)
% 15.79/16.00          | ~ (m1_subset_1 @ X9 @ X10))),
% 15.79/16.00      inference('cnf', [status(esa)], [t2_subset])).
% 15.79/16.00  thf('33', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 15.79/16.00      inference('sup-', [status(thm)], ['31', '32'])).
% 15.79/16.00  thf(l13_xboole_0, axiom,
% 15.79/16.00    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 15.79/16.00  thf('34', plain,
% 15.79/16.00      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 15.79/16.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.79/16.00  thf('35', plain,
% 15.79/16.00      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 15.79/16.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 15.79/16.00  thf('36', plain,
% 15.79/16.00      (![X0 : $i, X1 : $i]:
% 15.79/16.00         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 15.79/16.00      inference('sup+', [status(thm)], ['34', '35'])).
% 15.79/16.00  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('38', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (((X0) != (k1_xboole_0))
% 15.79/16.00          | ~ (v1_xboole_0 @ X0)
% 15.79/16.00          | ~ (v1_xboole_0 @ sk_B_1))),
% 15.79/16.00      inference('sup-', [status(thm)], ['36', '37'])).
% 15.79/16.00  thf('39', plain,
% 15.79/16.00      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 15.79/16.00      inference('simplify', [status(thm)], ['38'])).
% 15.79/16.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.79/16.00  thf('40', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 15.79/16.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.79/16.00  thf(d1_xboole_0, axiom,
% 15.79/16.00    (![A:$i]:
% 15.79/16.00     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 15.79/16.00  thf('41', plain,
% 15.79/16.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 15.79/16.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 15.79/16.00  thf(t7_ordinal1, axiom,
% 15.79/16.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.79/16.00  thf('42', plain,
% 15.79/16.00      (![X18 : $i, X19 : $i]:
% 15.79/16.00         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 15.79/16.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 15.79/16.00  thf('43', plain,
% 15.79/16.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 15.79/16.00      inference('sup-', [status(thm)], ['41', '42'])).
% 15.79/16.00  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 15.79/16.00      inference('sup-', [status(thm)], ['40', '43'])).
% 15.79/16.00  thf('45', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 15.79/16.00      inference('demod', [status(thm)], ['39', '44'])).
% 15.79/16.00  thf('46', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 15.79/16.00      inference('clc', [status(thm)], ['33', '45'])).
% 15.79/16.00  thf('47', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(d1_funct_2, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.79/16.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.79/16.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 15.79/16.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 15.79/16.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.79/16.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 15.79/16.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 15.79/16.00  thf(zf_stmt_1, axiom,
% 15.79/16.00    (![C:$i,B:$i,A:$i]:
% 15.79/16.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 15.79/16.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 15.79/16.00  thf('48', plain,
% 15.79/16.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 15.79/16.00         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 15.79/16.00          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 15.79/16.00          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 15.79/16.00  thf('49', plain,
% 15.79/16.00      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 15.79/16.00        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 15.79/16.00      inference('sup-', [status(thm)], ['47', '48'])).
% 15.79/16.00  thf('50', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('51', plain,
% 15.79/16.00      (![X26 : $i, X27 : $i, X28 : $i]:
% 15.79/16.00         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 15.79/16.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 15.79/16.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 15.79/16.00  thf('52', plain,
% 15.79/16.00      (((k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['50', '51'])).
% 15.79/16.00  thf('53', plain,
% 15.79/16.00      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 15.79/16.00        | ((sk_B_1) = (k1_relat_1 @ sk_D_2)))),
% 15.79/16.00      inference('demod', [status(thm)], ['49', '52'])).
% 15.79/16.00  thf('54', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 15.79/16.00  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 15.79/16.00  thf(zf_stmt_4, axiom,
% 15.79/16.00    (![B:$i,A:$i]:
% 15.79/16.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 15.79/16.00       ( zip_tseitin_0 @ B @ A ) ))).
% 15.79/16.00  thf(zf_stmt_5, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.79/16.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 15.79/16.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 15.79/16.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 15.79/16.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 15.79/16.00  thf('55', plain,
% 15.79/16.00      (![X37 : $i, X38 : $i, X39 : $i]:
% 15.79/16.00         (~ (zip_tseitin_0 @ X37 @ X38)
% 15.79/16.00          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 15.79/16.00          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 15.79/16.00  thf('56', plain,
% 15.79/16.00      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 15.79/16.00        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B_1))),
% 15.79/16.00      inference('sup-', [status(thm)], ['54', '55'])).
% 15.79/16.00  thf('57', plain,
% 15.79/16.00      (![X32 : $i, X33 : $i]:
% 15.79/16.00         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_4])).
% 15.79/16.00  thf('58', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 15.79/16.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.79/16.00  thf('59', plain,
% 15.79/16.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.79/16.00         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 15.79/16.00      inference('sup+', [status(thm)], ['57', '58'])).
% 15.79/16.00  thf('60', plain,
% 15.79/16.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 15.79/16.00      inference('sup-', [status(thm)], ['41', '42'])).
% 15.79/16.00  thf('61', plain,
% 15.79/16.00      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 15.79/16.00      inference('sup-', [status(thm)], ['59', '60'])).
% 15.79/16.00  thf('62', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('63', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_2 @ X0)),
% 15.79/16.00      inference('sup-', [status(thm)], ['61', '62'])).
% 15.79/16.00  thf('64', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)),
% 15.79/16.00      inference('demod', [status(thm)], ['56', '63'])).
% 15.79/16.00  thf('65', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('demod', [status(thm)], ['53', '64'])).
% 15.79/16.00  thf(d5_funct_1, axiom,
% 15.79/16.00    (![A:$i]:
% 15.79/16.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 15.79/16.00       ( ![B:$i]:
% 15.79/16.00         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 15.79/16.00           ( ![C:$i]:
% 15.79/16.00             ( ( r2_hidden @ C @ B ) <=>
% 15.79/16.00               ( ?[D:$i]:
% 15.79/16.00                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 15.79/16.00                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 15.79/16.00  thf('66', plain,
% 15.79/16.00      (![X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 15.79/16.00         (((X14) != (k2_relat_1 @ X12))
% 15.79/16.00          | (r2_hidden @ X16 @ X14)
% 15.79/16.00          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 15.79/16.00          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 15.79/16.00          | ~ (v1_funct_1 @ X12)
% 15.79/16.00          | ~ (v1_relat_1 @ X12))),
% 15.79/16.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 15.79/16.00  thf('67', plain,
% 15.79/16.00      (![X12 : $i, X17 : $i]:
% 15.79/16.00         (~ (v1_relat_1 @ X12)
% 15.79/16.00          | ~ (v1_funct_1 @ X12)
% 15.79/16.00          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 15.79/16.00          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 15.79/16.00      inference('simplify', [status(thm)], ['66'])).
% 15.79/16.00  thf('68', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (~ (r2_hidden @ X0 @ sk_B_1)
% 15.79/16.00          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 15.79/16.00          | ~ (v1_funct_1 @ sk_D_2)
% 15.79/16.00          | ~ (v1_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['65', '67'])).
% 15.79/16.00  thf('69', plain, ((v1_funct_1 @ sk_D_2)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('70', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(cc1_relset_1, axiom,
% 15.79/16.00    (![A:$i,B:$i,C:$i]:
% 15.79/16.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 15.79/16.00       ( v1_relat_1 @ C ) ))).
% 15.79/16.00  thf('71', plain,
% 15.79/16.00      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.79/16.00         ((v1_relat_1 @ X20)
% 15.79/16.00          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 15.79/16.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.79/16.00  thf('72', plain, ((v1_relat_1 @ sk_D_2)),
% 15.79/16.00      inference('sup-', [status(thm)], ['70', '71'])).
% 15.79/16.00  thf('73', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (~ (r2_hidden @ X0 @ sk_B_1)
% 15.79/16.00          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 15.79/16.00      inference('demod', [status(thm)], ['68', '69', '72'])).
% 15.79/16.00  thf('74', plain,
% 15.79/16.00      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k2_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['46', '73'])).
% 15.79/16.00  thf('75', plain,
% 15.79/16.00      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) @ 
% 15.79/16.00        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf(d3_tarski, axiom,
% 15.79/16.00    (![A:$i,B:$i]:
% 15.79/16.00     ( ( r1_tarski @ A @ B ) <=>
% 15.79/16.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 15.79/16.00  thf('76', plain,
% 15.79/16.00      (![X3 : $i, X4 : $i, X5 : $i]:
% 15.79/16.00         (~ (r2_hidden @ X3 @ X4)
% 15.79/16.00          | (r2_hidden @ X3 @ X5)
% 15.79/16.00          | ~ (r1_tarski @ X4 @ X5))),
% 15.79/16.00      inference('cnf', [status(esa)], [d3_tarski])).
% 15.79/16.00  thf('77', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 15.79/16.00          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 15.79/16.00      inference('sup-', [status(thm)], ['75', '76'])).
% 15.79/16.00  thf('78', plain,
% 15.79/16.00      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 15.79/16.00      inference('sup-', [status(thm)], ['1', '2'])).
% 15.79/16.00  thf('79', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 15.79/16.00          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 15.79/16.00      inference('demod', [status(thm)], ['77', '78'])).
% 15.79/16.00  thf('80', plain,
% 15.79/16.00      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 15.79/16.00      inference('sup-', [status(thm)], ['7', '8'])).
% 15.79/16.00  thf('81', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 15.79/16.00          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 15.79/16.00      inference('demod', [status(thm)], ['79', '80'])).
% 15.79/16.00  thf('82', plain,
% 15.79/16.00      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 15.79/16.00      inference('sup-', [status(thm)], ['74', '81'])).
% 15.79/16.00  thf(d8_partfun1, axiom,
% 15.79/16.00    (![A:$i,B:$i]:
% 15.79/16.00     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 15.79/16.00       ( ![C:$i]:
% 15.79/16.00         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 15.79/16.00           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 15.79/16.00  thf('83', plain,
% 15.79/16.00      (![X40 : $i, X41 : $i, X42 : $i]:
% 15.79/16.00         (~ (r2_hidden @ X40 @ (k1_relat_1 @ X41))
% 15.79/16.00          | ((k7_partfun1 @ X42 @ X41 @ X40) = (k1_funct_1 @ X41 @ X40))
% 15.79/16.00          | ~ (v1_funct_1 @ X41)
% 15.79/16.00          | ~ (v5_relat_1 @ X41 @ X42)
% 15.79/16.00          | ~ (v1_relat_1 @ X41))),
% 15.79/16.00      inference('cnf', [status(esa)], [d8_partfun1])).
% 15.79/16.00  thf('84', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (~ (v1_relat_1 @ sk_E)
% 15.79/16.00          | ~ (v5_relat_1 @ sk_E @ X0)
% 15.79/16.00          | ~ (v1_funct_1 @ sk_E)
% 15.79/16.00          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 15.79/16.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 15.79/16.00      inference('sup-', [status(thm)], ['82', '83'])).
% 15.79/16.00  thf('85', plain,
% 15.79/16.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('86', plain,
% 15.79/16.00      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.79/16.00         ((v1_relat_1 @ X20)
% 15.79/16.00          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 15.79/16.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 15.79/16.00  thf('87', plain, ((v1_relat_1 @ sk_E)),
% 15.79/16.00      inference('sup-', [status(thm)], ['85', '86'])).
% 15.79/16.00  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 15.79/16.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.79/16.00  thf('89', plain,
% 15.79/16.00      (![X0 : $i]:
% 15.79/16.00         (~ (v5_relat_1 @ sk_E @ X0)
% 15.79/16.00          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 15.79/16.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 15.79/16.00      inference('demod', [status(thm)], ['84', '87', '88'])).
% 15.79/16.00  thf('90', plain,
% 15.79/16.00      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 15.79/16.00         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.79/16.00      inference('sup-', [status(thm)], ['30', '89'])).
% 15.79/16.00  thf('91', plain,
% 15.79/16.00      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 15.79/16.00         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 15.79/16.00      inference('demod', [status(thm)], ['27', '90'])).
% 15.79/16.00  thf('92', plain, ($false),
% 15.79/16.00      inference('simplify_reflect-', [status(thm)], ['26', '91'])).
% 15.79/16.00  
% 15.79/16.00  % SZS output end Refutation
% 15.79/16.00  
% 15.79/16.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
