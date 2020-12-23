%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JUdmrcNRW4

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:09 EST 2020

% Result     : Theorem 18.73s
% Output     : Refutation 18.73s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 221 expanded)
%              Number of leaves         :   49 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          : 1182 (4190 expanded)
%              Number of equality atoms :   59 ( 178 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X40 @ X41 @ X44 @ X39 @ X43 ) @ X42 )
        = ( k1_funct_1 @ X43 @ ( k1_funct_1 @ X39 @ X42 ) ) )
      | ( X40 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X40 @ X41 @ X39 ) @ ( k1_relset_1 @ X41 @ X44 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
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
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['53','64'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X15 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','72','73'])).

thf('75',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','74'])).

thf('76',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('77',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('82',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X37 ) )
      | ( ( k7_partfun1 @ X38 @ X37 @ X36 )
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v5_relat_1 @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['83','88','89'])).

thf('91',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','90'])).

thf('92',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','91'])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JUdmrcNRW4
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 18.73/18.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.73/18.94  % Solved by: fo/fo7.sh
% 18.73/18.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.73/18.94  % done 8049 iterations in 18.485s
% 18.73/18.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.73/18.94  % SZS output start Refutation
% 18.73/18.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 18.73/18.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.73/18.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 18.73/18.94  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 18.73/18.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 18.73/18.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.73/18.94  thf(sk_A_type, type, sk_A: $i).
% 18.73/18.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.73/18.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 18.73/18.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.73/18.94  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 18.73/18.94  thf(sk_B_1_type, type, sk_B_1: $i).
% 18.73/18.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 18.73/18.94  thf(sk_E_type, type, sk_E: $i).
% 18.73/18.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.73/18.94  thf(sk_F_type, type, sk_F: $i).
% 18.73/18.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 18.73/18.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 18.73/18.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 18.73/18.94  thf(sk_D_type, type, sk_D: $i).
% 18.73/18.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.73/18.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 18.73/18.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 18.73/18.94  thf(sk_B_type, type, sk_B: $i > $i).
% 18.73/18.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.73/18.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 18.73/18.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.73/18.94  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 18.73/18.94  thf(t186_funct_2, conjecture,
% 18.73/18.94    (![A:$i,B:$i,C:$i]:
% 18.73/18.94     ( ( ~( v1_xboole_0 @ C ) ) =>
% 18.73/18.94       ( ![D:$i]:
% 18.73/18.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 18.73/18.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 18.73/18.94           ( ![E:$i]:
% 18.73/18.94             ( ( ( v1_funct_1 @ E ) & 
% 18.73/18.94                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 18.73/18.94               ( ![F:$i]:
% 18.73/18.94                 ( ( m1_subset_1 @ F @ B ) =>
% 18.73/18.94                   ( ( r1_tarski @
% 18.73/18.94                       ( k2_relset_1 @ B @ C @ D ) @ 
% 18.73/18.94                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 18.73/18.94                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.73/18.94                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 18.73/18.94                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 18.73/18.94  thf(zf_stmt_0, negated_conjecture,
% 18.73/18.94    (~( ![A:$i,B:$i,C:$i]:
% 18.73/18.94        ( ( ~( v1_xboole_0 @ C ) ) =>
% 18.73/18.94          ( ![D:$i]:
% 18.73/18.94            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 18.73/18.94                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 18.73/18.94              ( ![E:$i]:
% 18.73/18.94                ( ( ( v1_funct_1 @ E ) & 
% 18.73/18.94                    ( m1_subset_1 @
% 18.73/18.94                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 18.73/18.94                  ( ![F:$i]:
% 18.73/18.94                    ( ( m1_subset_1 @ F @ B ) =>
% 18.73/18.94                      ( ( r1_tarski @
% 18.73/18.94                          ( k2_relset_1 @ B @ C @ D ) @ 
% 18.73/18.94                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 18.73/18.94                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.73/18.94                          ( ( k1_funct_1 @
% 18.73/18.94                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 18.73/18.94                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 18.73/18.94    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 18.73/18.94  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('1', plain,
% 18.73/18.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf(redefinition_k1_relset_1, axiom,
% 18.73/18.94    (![A:$i,B:$i,C:$i]:
% 18.73/18.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.73/18.94       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 18.73/18.94  thf('2', plain,
% 18.73/18.94      (![X22 : $i, X23 : $i, X24 : $i]:
% 18.73/18.94         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 18.73/18.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 18.73/18.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.73/18.94  thf('3', plain,
% 18.73/18.94      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 18.73/18.94      inference('sup-', [status(thm)], ['1', '2'])).
% 18.73/18.94  thf('4', plain,
% 18.73/18.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf(t185_funct_2, axiom,
% 18.73/18.94    (![A:$i,B:$i,C:$i]:
% 18.73/18.94     ( ( ~( v1_xboole_0 @ C ) ) =>
% 18.73/18.94       ( ![D:$i]:
% 18.73/18.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 18.73/18.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 18.73/18.94           ( ![E:$i]:
% 18.73/18.94             ( ( ( v1_funct_1 @ E ) & 
% 18.73/18.94                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 18.73/18.94               ( ![F:$i]:
% 18.73/18.94                 ( ( m1_subset_1 @ F @ B ) =>
% 18.73/18.94                   ( ( r1_tarski @
% 18.73/18.94                       ( k2_relset_1 @ B @ C @ D ) @ 
% 18.73/18.94                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 18.73/18.94                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 18.73/18.94                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 18.73/18.94                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 18.73/18.94  thf('5', plain,
% 18.73/18.94      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 18.73/18.94         (~ (v1_funct_1 @ X39)
% 18.73/18.94          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 18.73/18.94          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 18.73/18.94          | ~ (m1_subset_1 @ X42 @ X40)
% 18.73/18.94          | ((k1_funct_1 @ (k8_funct_2 @ X40 @ X41 @ X44 @ X39 @ X43) @ X42)
% 18.73/18.94              = (k1_funct_1 @ X43 @ (k1_funct_1 @ X39 @ X42)))
% 18.73/18.94          | ((X40) = (k1_xboole_0))
% 18.73/18.94          | ~ (r1_tarski @ (k2_relset_1 @ X40 @ X41 @ X39) @ 
% 18.73/18.94               (k1_relset_1 @ X41 @ X44 @ X43))
% 18.73/18.94          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X44)))
% 18.73/18.94          | ~ (v1_funct_1 @ X43)
% 18.73/18.94          | (v1_xboole_0 @ X41))),
% 18.73/18.94      inference('cnf', [status(esa)], [t185_funct_2])).
% 18.73/18.94  thf('6', plain,
% 18.73/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.73/18.94         ((v1_xboole_0 @ sk_C_1)
% 18.73/18.94          | ~ (v1_funct_1 @ X0)
% 18.73/18.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 18.73/18.94          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 18.73/18.94               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 18.73/18.94          | ((sk_B_1) = (k1_xboole_0))
% 18.73/18.94          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 18.73/18.94              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 18.73/18.94          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 18.73/18.94          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 18.73/18.94          | ~ (v1_funct_1 @ sk_D))),
% 18.73/18.94      inference('sup-', [status(thm)], ['4', '5'])).
% 18.73/18.94  thf('7', plain,
% 18.73/18.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf(redefinition_k2_relset_1, axiom,
% 18.73/18.94    (![A:$i,B:$i,C:$i]:
% 18.73/18.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.73/18.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 18.73/18.94  thf('8', plain,
% 18.73/18.94      (![X25 : $i, X26 : $i, X27 : $i]:
% 18.73/18.94         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 18.73/18.94          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 18.73/18.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 18.73/18.94  thf('9', plain,
% 18.73/18.94      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 18.73/18.94      inference('sup-', [status(thm)], ['7', '8'])).
% 18.73/18.94  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('12', plain,
% 18.73/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.73/18.94         ((v1_xboole_0 @ sk_C_1)
% 18.73/18.94          | ~ (v1_funct_1 @ X0)
% 18.73/18.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 18.73/18.94          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 18.73/18.94               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 18.73/18.94          | ((sk_B_1) = (k1_xboole_0))
% 18.73/18.94          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 18.73/18.94              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 18.73/18.94          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 18.73/18.94      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 18.73/18.94  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('14', plain,
% 18.73/18.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.73/18.94         ((v1_xboole_0 @ sk_C_1)
% 18.73/18.94          | ~ (v1_funct_1 @ X0)
% 18.73/18.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 18.73/18.94          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 18.73/18.94               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 18.73/18.94          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 18.73/18.94              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 18.73/18.94          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 18.73/18.94      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 18.73/18.94  thf('15', plain,
% 18.73/18.94      (![X0 : $i]:
% 18.73/18.94         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 18.73/18.94          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 18.73/18.94          | ((k1_funct_1 @ 
% 18.73/18.94              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 18.73/18.94              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 18.73/18.94          | ~ (m1_subset_1 @ sk_E @ 
% 18.73/18.94               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 18.73/18.94          | ~ (v1_funct_1 @ sk_E)
% 18.73/18.94          | (v1_xboole_0 @ sk_C_1))),
% 18.73/18.94      inference('sup-', [status(thm)], ['3', '14'])).
% 18.73/18.94  thf('16', plain,
% 18.73/18.94      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 18.73/18.94        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('17', plain,
% 18.73/18.94      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 18.73/18.94      inference('sup-', [status(thm)], ['1', '2'])).
% 18.73/18.94  thf('18', plain,
% 18.73/18.94      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 18.73/18.94        (k1_relat_1 @ sk_E))),
% 18.73/18.94      inference('demod', [status(thm)], ['16', '17'])).
% 18.73/18.94  thf('19', plain,
% 18.73/18.94      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 18.73/18.94      inference('sup-', [status(thm)], ['7', '8'])).
% 18.73/18.94  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 18.73/18.94      inference('demod', [status(thm)], ['18', '19'])).
% 18.73/18.94  thf('21', plain,
% 18.73/18.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('23', plain,
% 18.73/18.94      (![X0 : $i]:
% 18.73/18.94         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 18.73/18.94          | ((k1_funct_1 @ 
% 18.73/18.94              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 18.73/18.94              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 18.73/18.94          | (v1_xboole_0 @ sk_C_1))),
% 18.73/18.94      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 18.73/18.94  thf('24', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('25', plain,
% 18.73/18.94      (![X0 : $i]:
% 18.73/18.94         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 18.73/18.94            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 18.73/18.94          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 18.73/18.94      inference('clc', [status(thm)], ['23', '24'])).
% 18.73/18.94  thf('26', plain,
% 18.73/18.94      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 18.73/18.94         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 18.73/18.94      inference('sup-', [status(thm)], ['0', '25'])).
% 18.73/18.94  thf('27', plain,
% 18.73/18.94      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 18.73/18.94         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('28', plain,
% 18.73/18.94      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf(cc2_relset_1, axiom,
% 18.73/18.94    (![A:$i,B:$i,C:$i]:
% 18.73/18.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.73/18.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 18.73/18.94  thf('29', plain,
% 18.73/18.94      (![X19 : $i, X20 : $i, X21 : $i]:
% 18.73/18.94         ((v5_relat_1 @ X19 @ X21)
% 18.73/18.94          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 18.73/18.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 18.73/18.94  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 18.73/18.94      inference('sup-', [status(thm)], ['28', '29'])).
% 18.73/18.94  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf(t2_subset, axiom,
% 18.73/18.94    (![A:$i,B:$i]:
% 18.73/18.94     ( ( m1_subset_1 @ A @ B ) =>
% 18.73/18.94       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 18.73/18.94  thf('32', plain,
% 18.73/18.94      (![X9 : $i, X10 : $i]:
% 18.73/18.94         ((r2_hidden @ X9 @ X10)
% 18.73/18.94          | (v1_xboole_0 @ X10)
% 18.73/18.94          | ~ (m1_subset_1 @ X9 @ X10))),
% 18.73/18.94      inference('cnf', [status(esa)], [t2_subset])).
% 18.73/18.94  thf('33', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 18.73/18.94      inference('sup-', [status(thm)], ['31', '32'])).
% 18.73/18.94  thf(l13_xboole_0, axiom,
% 18.73/18.94    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 18.73/18.94  thf('34', plain,
% 18.73/18.94      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 18.73/18.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 18.73/18.94  thf('35', plain,
% 18.73/18.94      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 18.73/18.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 18.73/18.94  thf('36', plain,
% 18.73/18.94      (![X0 : $i, X1 : $i]:
% 18.73/18.94         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 18.73/18.94      inference('sup+', [status(thm)], ['34', '35'])).
% 18.73/18.94  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 18.73/18.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.94  thf('38', plain,
% 18.73/18.94      (![X0 : $i]:
% 18.73/18.94         (((X0) != (k1_xboole_0))
% 18.73/18.94          | ~ (v1_xboole_0 @ X0)
% 18.73/18.94          | ~ (v1_xboole_0 @ sk_B_1))),
% 18.73/18.94      inference('sup-', [status(thm)], ['36', '37'])).
% 18.73/18.94  thf('39', plain,
% 18.73/18.94      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 18.73/18.94      inference('simplify', [status(thm)], ['38'])).
% 18.73/18.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 18.73/18.94  thf('40', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 18.73/18.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 18.73/18.94  thf(d1_xboole_0, axiom,
% 18.73/18.94    (![A:$i]:
% 18.73/18.94     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 18.73/18.94  thf('41', plain,
% 18.73/18.94      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 18.73/18.94      inference('cnf', [status(esa)], [d1_xboole_0])).
% 18.73/18.94  thf(t7_ordinal1, axiom,
% 18.73/18.94    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 18.73/18.94  thf('42', plain,
% 18.73/18.94      (![X17 : $i, X18 : $i]:
% 18.73/18.94         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 18.73/18.94      inference('cnf', [status(esa)], [t7_ordinal1])).
% 18.73/18.94  thf('43', plain,
% 18.73/18.94      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 18.73/18.95      inference('sup-', [status(thm)], ['41', '42'])).
% 18.73/18.95  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 18.73/18.95      inference('sup-', [status(thm)], ['40', '43'])).
% 18.73/18.95  thf('45', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 18.73/18.95      inference('demod', [status(thm)], ['39', '44'])).
% 18.73/18.95  thf('46', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 18.73/18.95      inference('clc', [status(thm)], ['33', '45'])).
% 18.73/18.95  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf(d1_funct_2, axiom,
% 18.73/18.95    (![A:$i,B:$i,C:$i]:
% 18.73/18.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.73/18.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.73/18.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 18.73/18.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 18.73/18.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.73/18.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 18.73/18.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 18.73/18.95  thf(zf_stmt_1, axiom,
% 18.73/18.95    (![C:$i,B:$i,A:$i]:
% 18.73/18.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 18.73/18.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 18.73/18.95  thf('48', plain,
% 18.73/18.95      (![X30 : $i, X31 : $i, X32 : $i]:
% 18.73/18.95         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 18.73/18.95          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 18.73/18.95          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.73/18.95  thf('49', plain,
% 18.73/18.95      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 18.73/18.95        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 18.73/18.95      inference('sup-', [status(thm)], ['47', '48'])).
% 18.73/18.95  thf('50', plain,
% 18.73/18.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf('51', plain,
% 18.73/18.95      (![X22 : $i, X23 : $i, X24 : $i]:
% 18.73/18.95         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 18.73/18.95          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 18.73/18.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 18.73/18.95  thf('52', plain,
% 18.73/18.95      (((k1_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 18.73/18.95      inference('sup-', [status(thm)], ['50', '51'])).
% 18.73/18.95  thf('53', plain,
% 18.73/18.95      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 18.73/18.95        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 18.73/18.95      inference('demod', [status(thm)], ['49', '52'])).
% 18.73/18.95  thf('54', plain,
% 18.73/18.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 18.73/18.95  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 18.73/18.95  thf(zf_stmt_4, axiom,
% 18.73/18.95    (![B:$i,A:$i]:
% 18.73/18.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 18.73/18.95       ( zip_tseitin_0 @ B @ A ) ))).
% 18.73/18.95  thf(zf_stmt_5, axiom,
% 18.73/18.95    (![A:$i,B:$i,C:$i]:
% 18.73/18.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 18.73/18.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 18.73/18.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 18.73/18.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 18.73/18.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 18.73/18.95  thf('55', plain,
% 18.73/18.95      (![X33 : $i, X34 : $i, X35 : $i]:
% 18.73/18.95         (~ (zip_tseitin_0 @ X33 @ X34)
% 18.73/18.95          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 18.73/18.95          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 18.73/18.95  thf('56', plain,
% 18.73/18.95      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)
% 18.73/18.95        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B_1))),
% 18.73/18.95      inference('sup-', [status(thm)], ['54', '55'])).
% 18.73/18.95  thf('57', plain,
% 18.73/18.95      (![X28 : $i, X29 : $i]:
% 18.73/18.95         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_4])).
% 18.73/18.95  thf('58', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 18.73/18.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 18.73/18.95  thf('59', plain,
% 18.73/18.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.73/18.95         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 18.73/18.95      inference('sup+', [status(thm)], ['57', '58'])).
% 18.73/18.95  thf('60', plain,
% 18.73/18.95      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 18.73/18.95      inference('sup-', [status(thm)], ['41', '42'])).
% 18.73/18.95  thf('61', plain,
% 18.73/18.95      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 18.73/18.95      inference('sup-', [status(thm)], ['59', '60'])).
% 18.73/18.95  thf('62', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf('63', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 18.73/18.95      inference('sup-', [status(thm)], ['61', '62'])).
% 18.73/18.95  thf('64', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B_1)),
% 18.73/18.95      inference('demod', [status(thm)], ['56', '63'])).
% 18.73/18.95  thf('65', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 18.73/18.95      inference('demod', [status(thm)], ['53', '64'])).
% 18.73/18.95  thf(t12_funct_1, axiom,
% 18.73/18.95    (![A:$i,B:$i]:
% 18.73/18.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.73/18.95       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 18.73/18.95         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 18.73/18.95  thf('66', plain,
% 18.73/18.95      (![X15 : $i, X16 : $i]:
% 18.73/18.95         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 18.73/18.95          | (r2_hidden @ (k1_funct_1 @ X16 @ X15) @ (k2_relat_1 @ X16))
% 18.73/18.95          | ~ (v1_funct_1 @ X16)
% 18.73/18.95          | ~ (v1_relat_1 @ X16))),
% 18.73/18.95      inference('cnf', [status(esa)], [t12_funct_1])).
% 18.73/18.95  thf('67', plain,
% 18.73/18.95      (![X0 : $i]:
% 18.73/18.95         (~ (r2_hidden @ X0 @ sk_B_1)
% 18.73/18.95          | ~ (v1_relat_1 @ sk_D)
% 18.73/18.95          | ~ (v1_funct_1 @ sk_D)
% 18.73/18.95          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 18.73/18.95      inference('sup-', [status(thm)], ['65', '66'])).
% 18.73/18.95  thf('68', plain,
% 18.73/18.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf(cc2_relat_1, axiom,
% 18.73/18.95    (![A:$i]:
% 18.73/18.95     ( ( v1_relat_1 @ A ) =>
% 18.73/18.95       ( ![B:$i]:
% 18.73/18.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 18.73/18.95  thf('69', plain,
% 18.73/18.95      (![X11 : $i, X12 : $i]:
% 18.73/18.95         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 18.73/18.95          | (v1_relat_1 @ X11)
% 18.73/18.95          | ~ (v1_relat_1 @ X12))),
% 18.73/18.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.73/18.95  thf('70', plain,
% 18.73/18.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)) | (v1_relat_1 @ sk_D))),
% 18.73/18.95      inference('sup-', [status(thm)], ['68', '69'])).
% 18.73/18.95  thf(fc6_relat_1, axiom,
% 18.73/18.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 18.73/18.95  thf('71', plain,
% 18.73/18.95      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 18.73/18.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.73/18.95  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 18.73/18.95      inference('demod', [status(thm)], ['70', '71'])).
% 18.73/18.95  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf('74', plain,
% 18.73/18.95      (![X0 : $i]:
% 18.73/18.95         (~ (r2_hidden @ X0 @ sk_B_1)
% 18.73/18.95          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 18.73/18.95      inference('demod', [status(thm)], ['67', '72', '73'])).
% 18.73/18.95  thf('75', plain,
% 18.73/18.95      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))),
% 18.73/18.95      inference('sup-', [status(thm)], ['46', '74'])).
% 18.73/18.95  thf('76', plain,
% 18.73/18.95      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 18.73/18.95        (k1_relat_1 @ sk_E))),
% 18.73/18.95      inference('demod', [status(thm)], ['16', '17'])).
% 18.73/18.95  thf(d3_tarski, axiom,
% 18.73/18.95    (![A:$i,B:$i]:
% 18.73/18.95     ( ( r1_tarski @ A @ B ) <=>
% 18.73/18.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 18.73/18.95  thf('77', plain,
% 18.73/18.95      (![X3 : $i, X4 : $i, X5 : $i]:
% 18.73/18.95         (~ (r2_hidden @ X3 @ X4)
% 18.73/18.95          | (r2_hidden @ X3 @ X5)
% 18.73/18.95          | ~ (r1_tarski @ X4 @ X5))),
% 18.73/18.95      inference('cnf', [status(esa)], [d3_tarski])).
% 18.73/18.95  thf('78', plain,
% 18.73/18.95      (![X0 : $i]:
% 18.73/18.95         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 18.73/18.95          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 18.73/18.95      inference('sup-', [status(thm)], ['76', '77'])).
% 18.73/18.95  thf('79', plain,
% 18.73/18.95      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 18.73/18.95      inference('sup-', [status(thm)], ['7', '8'])).
% 18.73/18.95  thf('80', plain,
% 18.73/18.95      (![X0 : $i]:
% 18.73/18.95         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 18.73/18.95          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 18.73/18.95      inference('demod', [status(thm)], ['78', '79'])).
% 18.73/18.95  thf('81', plain,
% 18.73/18.95      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 18.73/18.95      inference('sup-', [status(thm)], ['75', '80'])).
% 18.73/18.95  thf(d8_partfun1, axiom,
% 18.73/18.95    (![A:$i,B:$i]:
% 18.73/18.95     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 18.73/18.95       ( ![C:$i]:
% 18.73/18.95         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 18.73/18.95           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 18.73/18.95  thf('82', plain,
% 18.73/18.95      (![X36 : $i, X37 : $i, X38 : $i]:
% 18.73/18.95         (~ (r2_hidden @ X36 @ (k1_relat_1 @ X37))
% 18.73/18.95          | ((k7_partfun1 @ X38 @ X37 @ X36) = (k1_funct_1 @ X37 @ X36))
% 18.73/18.95          | ~ (v1_funct_1 @ X37)
% 18.73/18.95          | ~ (v5_relat_1 @ X37 @ X38)
% 18.73/18.95          | ~ (v1_relat_1 @ X37))),
% 18.73/18.95      inference('cnf', [status(esa)], [d8_partfun1])).
% 18.73/18.95  thf('83', plain,
% 18.73/18.95      (![X0 : $i]:
% 18.73/18.95         (~ (v1_relat_1 @ sk_E)
% 18.73/18.95          | ~ (v5_relat_1 @ sk_E @ X0)
% 18.73/18.95          | ~ (v1_funct_1 @ sk_E)
% 18.73/18.95          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 18.73/18.95              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 18.73/18.95      inference('sup-', [status(thm)], ['81', '82'])).
% 18.73/18.95  thf('84', plain,
% 18.73/18.95      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf('85', plain,
% 18.73/18.95      (![X11 : $i, X12 : $i]:
% 18.73/18.95         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 18.73/18.95          | (v1_relat_1 @ X11)
% 18.73/18.95          | ~ (v1_relat_1 @ X12))),
% 18.73/18.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 18.73/18.95  thf('86', plain,
% 18.73/18.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 18.73/18.95      inference('sup-', [status(thm)], ['84', '85'])).
% 18.73/18.95  thf('87', plain,
% 18.73/18.95      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 18.73/18.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 18.73/18.95  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 18.73/18.95      inference('demod', [status(thm)], ['86', '87'])).
% 18.73/18.95  thf('89', plain, ((v1_funct_1 @ sk_E)),
% 18.73/18.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.73/18.95  thf('90', plain,
% 18.73/18.95      (![X0 : $i]:
% 18.73/18.95         (~ (v5_relat_1 @ sk_E @ X0)
% 18.73/18.95          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 18.73/18.95              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 18.73/18.95      inference('demod', [status(thm)], ['83', '88', '89'])).
% 18.73/18.95  thf('91', plain,
% 18.73/18.95      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 18.73/18.95         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 18.73/18.95      inference('sup-', [status(thm)], ['30', '90'])).
% 18.73/18.95  thf('92', plain,
% 18.73/18.95      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 18.73/18.95         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 18.73/18.95      inference('demod', [status(thm)], ['27', '91'])).
% 18.73/18.95  thf('93', plain, ($false),
% 18.73/18.95      inference('simplify_reflect-', [status(thm)], ['26', '92'])).
% 18.73/18.95  
% 18.73/18.95  % SZS output end Refutation
% 18.73/18.95  
% 18.73/18.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
