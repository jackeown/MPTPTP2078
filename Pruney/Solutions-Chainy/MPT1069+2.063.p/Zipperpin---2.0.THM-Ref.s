%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LbmaAd2ENE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:09 EST 2020

% Result     : Theorem 26.43s
% Output     : Refutation 26.43s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 208 expanded)
%              Number of leaves         :   46 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          : 1175 (4143 expanded)
%              Number of equality atoms :   63 ( 181 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_F @ sk_B ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
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

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 ),
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
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
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
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['33','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 ),
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

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
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

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['45','54','57'])).

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

thf('59',plain,(
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

thf('60',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['61','62','67'])).

thf('69',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['42','68'])).

thf('70',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('78',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( ( k7_partfun1 @ X37 @ X36 @ X35 )
        = ( k1_funct_1 @ X36 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['79','84','85'])).

thf('87',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','86'])).

thf('88',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LbmaAd2ENE
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 26.43/26.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.43/26.68  % Solved by: fo/fo7.sh
% 26.43/26.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.43/26.68  % done 6238 iterations in 26.238s
% 26.43/26.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.43/26.68  % SZS output start Refutation
% 26.43/26.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 26.43/26.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 26.43/26.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 26.43/26.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 26.43/26.68  thf(sk_C_2_type, type, sk_C_2: $i).
% 26.43/26.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.43/26.68  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 26.43/26.68  thf(sk_F_type, type, sk_F: $i).
% 26.43/26.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.43/26.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 26.43/26.68  thf(sk_B_type, type, sk_B: $i).
% 26.43/26.68  thf(sk_E_type, type, sk_E: $i).
% 26.43/26.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 26.43/26.68  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 26.43/26.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 26.43/26.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 26.43/26.68  thf(sk_D_2_type, type, sk_D_2: $i).
% 26.43/26.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.43/26.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 26.43/26.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.43/26.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 26.43/26.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 26.43/26.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 26.43/26.68  thf(sk_A_type, type, sk_A: $i).
% 26.43/26.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 26.43/26.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 26.43/26.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.43/26.68  thf(t186_funct_2, conjecture,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( ~( v1_xboole_0 @ C ) ) =>
% 26.43/26.68       ( ![D:$i]:
% 26.43/26.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 26.43/26.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 26.43/26.68           ( ![E:$i]:
% 26.43/26.68             ( ( ( v1_funct_1 @ E ) & 
% 26.43/26.68                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 26.43/26.68               ( ![F:$i]:
% 26.43/26.68                 ( ( m1_subset_1 @ F @ B ) =>
% 26.43/26.68                   ( ( r1_tarski @
% 26.43/26.68                       ( k2_relset_1 @ B @ C @ D ) @ 
% 26.43/26.68                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 26.43/26.68                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 26.43/26.68                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 26.43/26.68                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 26.43/26.68  thf(zf_stmt_0, negated_conjecture,
% 26.43/26.68    (~( ![A:$i,B:$i,C:$i]:
% 26.43/26.68        ( ( ~( v1_xboole_0 @ C ) ) =>
% 26.43/26.68          ( ![D:$i]:
% 26.43/26.68            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 26.43/26.68                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 26.43/26.68              ( ![E:$i]:
% 26.43/26.68                ( ( ( v1_funct_1 @ E ) & 
% 26.43/26.68                    ( m1_subset_1 @
% 26.43/26.68                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 26.43/26.68                  ( ![F:$i]:
% 26.43/26.68                    ( ( m1_subset_1 @ F @ B ) =>
% 26.43/26.68                      ( ( r1_tarski @
% 26.43/26.68                          ( k2_relset_1 @ B @ C @ D ) @ 
% 26.43/26.68                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 26.43/26.68                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 26.43/26.68                          ( ( k1_funct_1 @
% 26.43/26.68                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 26.43/26.68                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 26.43/26.68    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 26.43/26.68  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('1', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(redefinition_k1_relset_1, axiom,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.43/26.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 26.43/26.68  thf('2', plain,
% 26.43/26.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 26.43/26.68         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 26.43/26.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 26.43/26.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 26.43/26.68  thf('3', plain,
% 26.43/26.68      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 26.43/26.68      inference('sup-', [status(thm)], ['1', '2'])).
% 26.43/26.68  thf('4', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(t185_funct_2, axiom,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( ~( v1_xboole_0 @ C ) ) =>
% 26.43/26.68       ( ![D:$i]:
% 26.43/26.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 26.43/26.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 26.43/26.68           ( ![E:$i]:
% 26.43/26.68             ( ( ( v1_funct_1 @ E ) & 
% 26.43/26.68                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 26.43/26.68               ( ![F:$i]:
% 26.43/26.68                 ( ( m1_subset_1 @ F @ B ) =>
% 26.43/26.68                   ( ( r1_tarski @
% 26.43/26.68                       ( k2_relset_1 @ B @ C @ D ) @ 
% 26.43/26.68                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 26.43/26.68                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 26.43/26.68                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 26.43/26.68                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 26.43/26.68  thf('5', plain,
% 26.43/26.68      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 26.43/26.68         (~ (v1_funct_1 @ X38)
% 26.43/26.68          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 26.43/26.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 26.43/26.68          | ~ (m1_subset_1 @ X41 @ X39)
% 26.43/26.68          | ((k1_funct_1 @ (k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42) @ X41)
% 26.43/26.68              = (k1_funct_1 @ X42 @ (k1_funct_1 @ X38 @ X41)))
% 26.43/26.68          | ((X39) = (k1_xboole_0))
% 26.43/26.68          | ~ (r1_tarski @ (k2_relset_1 @ X39 @ X40 @ X38) @ 
% 26.43/26.68               (k1_relset_1 @ X40 @ X43 @ X42))
% 26.43/26.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X43)))
% 26.43/26.68          | ~ (v1_funct_1 @ X42)
% 26.43/26.68          | (v1_xboole_0 @ X40))),
% 26.43/26.68      inference('cnf', [status(esa)], [t185_funct_2])).
% 26.43/26.68  thf('6', plain,
% 26.43/26.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.43/26.68         ((v1_xboole_0 @ sk_C_2)
% 26.43/26.68          | ~ (v1_funct_1 @ X0)
% 26.43/26.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 26.43/26.68          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 26.43/26.68               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 26.43/26.68          | ((sk_B) = (k1_xboole_0))
% 26.43/26.68          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 26.43/26.68              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 26.43/26.68          | ~ (m1_subset_1 @ X2 @ sk_B)
% 26.43/26.68          | ~ (v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)
% 26.43/26.68          | ~ (v1_funct_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['4', '5'])).
% 26.43/26.68  thf('7', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(redefinition_k2_relset_1, axiom,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.43/26.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 26.43/26.68  thf('8', plain,
% 26.43/26.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 26.43/26.68         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 26.43/26.68          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 26.43/26.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 26.43/26.68  thf('9', plain,
% 26.43/26.68      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['7', '8'])).
% 26.43/26.68  thf('10', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('11', plain, ((v1_funct_1 @ sk_D_2)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('12', plain,
% 26.43/26.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.43/26.68         ((v1_xboole_0 @ sk_C_2)
% 26.43/26.68          | ~ (v1_funct_1 @ X0)
% 26.43/26.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 26.43/26.68          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 26.43/26.68               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 26.43/26.68          | ((sk_B) = (k1_xboole_0))
% 26.43/26.68          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 26.43/26.68              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 26.43/26.68          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 26.43/26.68      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 26.43/26.68  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('14', plain,
% 26.43/26.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.43/26.68         ((v1_xboole_0 @ sk_C_2)
% 26.43/26.68          | ~ (v1_funct_1 @ X0)
% 26.43/26.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 26.43/26.68          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 26.43/26.68               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 26.43/26.68          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 26.43/26.68              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 26.43/26.68          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 26.43/26.68      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 26.43/26.68  thf('15', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 26.43/26.68          | ~ (m1_subset_1 @ X0 @ sk_B)
% 26.43/26.68          | ((k1_funct_1 @ 
% 26.43/26.68              (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 26.43/26.68              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 26.43/26.68          | ~ (m1_subset_1 @ sk_E @ 
% 26.43/26.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 26.43/26.68          | ~ (v1_funct_1 @ sk_E)
% 26.43/26.68          | (v1_xboole_0 @ sk_C_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['3', '14'])).
% 26.43/26.68  thf('16', plain,
% 26.43/26.68      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 26.43/26.68        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('17', plain,
% 26.43/26.68      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 26.43/26.68      inference('sup-', [status(thm)], ['1', '2'])).
% 26.43/26.68  thf('18', plain,
% 26.43/26.68      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 26.43/26.68        (k1_relat_1 @ sk_E))),
% 26.43/26.68      inference('demod', [status(thm)], ['16', '17'])).
% 26.43/26.68  thf('19', plain,
% 26.43/26.68      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['7', '8'])).
% 26.43/26.68  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 26.43/26.68      inference('demod', [status(thm)], ['18', '19'])).
% 26.43/26.68  thf('21', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('23', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (~ (m1_subset_1 @ X0 @ sk_B)
% 26.43/26.68          | ((k1_funct_1 @ 
% 26.43/26.68              (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 26.43/26.68              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 26.43/26.68          | (v1_xboole_0 @ sk_C_2))),
% 26.43/26.68      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 26.43/26.68  thf('24', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('25', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 26.43/26.68            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 26.43/26.68          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 26.43/26.68      inference('clc', [status(thm)], ['23', '24'])).
% 26.43/26.68  thf('26', plain,
% 26.43/26.68      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 26.43/26.68         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 26.43/26.68      inference('sup-', [status(thm)], ['0', '25'])).
% 26.43/26.68  thf('27', plain,
% 26.43/26.68      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 26.43/26.68         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('28', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(cc2_relset_1, axiom,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.43/26.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 26.43/26.68  thf('29', plain,
% 26.43/26.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.43/26.68         ((v5_relat_1 @ X18 @ X20)
% 26.43/26.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 26.43/26.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 26.43/26.68  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 26.43/26.68      inference('sup-', [status(thm)], ['28', '29'])).
% 26.43/26.68  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(t2_subset, axiom,
% 26.43/26.68    (![A:$i,B:$i]:
% 26.43/26.68     ( ( m1_subset_1 @ A @ B ) =>
% 26.43/26.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 26.43/26.68  thf('32', plain,
% 26.43/26.68      (![X5 : $i, X6 : $i]:
% 26.43/26.68         ((r2_hidden @ X5 @ X6)
% 26.43/26.68          | (v1_xboole_0 @ X6)
% 26.43/26.68          | ~ (m1_subset_1 @ X5 @ X6))),
% 26.43/26.68      inference('cnf', [status(esa)], [t2_subset])).
% 26.43/26.68  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 26.43/26.68      inference('sup-', [status(thm)], ['31', '32'])).
% 26.43/26.68  thf(l13_xboole_0, axiom,
% 26.43/26.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 26.43/26.68  thf('34', plain,
% 26.43/26.68      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 26.43/26.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 26.43/26.68  thf('35', plain,
% 26.43/26.68      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 26.43/26.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 26.43/26.68  thf('36', plain,
% 26.43/26.68      (![X0 : $i, X1 : $i]:
% 26.43/26.68         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 26.43/26.68      inference('sup+', [status(thm)], ['34', '35'])).
% 26.43/26.68  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('38', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (((X0) != (k1_xboole_0))
% 26.43/26.68          | ~ (v1_xboole_0 @ X0)
% 26.43/26.68          | ~ (v1_xboole_0 @ sk_B))),
% 26.43/26.68      inference('sup-', [status(thm)], ['36', '37'])).
% 26.43/26.68  thf('39', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 26.43/26.68      inference('simplify', [status(thm)], ['38'])).
% 26.43/26.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 26.43/26.68  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 26.43/26.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 26.43/26.68  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 26.43/26.68      inference('simplify_reflect+', [status(thm)], ['39', '40'])).
% 26.43/26.68  thf('42', plain, ((r2_hidden @ sk_F @ sk_B)),
% 26.43/26.68      inference('clc', [status(thm)], ['33', '41'])).
% 26.43/26.68  thf('43', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(d1_funct_2, axiom,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.43/26.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 26.43/26.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 26.43/26.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 26.43/26.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 26.43/26.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 26.43/26.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 26.43/26.68  thf(zf_stmt_1, axiom,
% 26.43/26.68    (![C:$i,B:$i,A:$i]:
% 26.43/26.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 26.43/26.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 26.43/26.68  thf('44', plain,
% 26.43/26.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 26.43/26.68         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 26.43/26.68          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 26.43/26.68          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.43/26.68  thf('45', plain,
% 26.43/26.68      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 26.43/26.68        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 26.43/26.68      inference('sup-', [status(thm)], ['43', '44'])).
% 26.43/26.68  thf('46', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 26.43/26.68  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 26.43/26.68  thf(zf_stmt_4, axiom,
% 26.43/26.68    (![B:$i,A:$i]:
% 26.43/26.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 26.43/26.68       ( zip_tseitin_0 @ B @ A ) ))).
% 26.43/26.68  thf(zf_stmt_5, axiom,
% 26.43/26.68    (![A:$i,B:$i,C:$i]:
% 26.43/26.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.43/26.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 26.43/26.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 26.43/26.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 26.43/26.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 26.43/26.68  thf('47', plain,
% 26.43/26.68      (![X32 : $i, X33 : $i, X34 : $i]:
% 26.43/26.68         (~ (zip_tseitin_0 @ X32 @ X33)
% 26.43/26.68          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 26.43/26.68          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 26.43/26.68  thf('48', plain,
% 26.43/26.68      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 26.43/26.68        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B))),
% 26.43/26.68      inference('sup-', [status(thm)], ['46', '47'])).
% 26.43/26.68  thf('49', plain,
% 26.43/26.68      (![X27 : $i, X28 : $i]:
% 26.43/26.68         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 26.43/26.68  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 26.43/26.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 26.43/26.68  thf('51', plain,
% 26.43/26.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 26.43/26.68      inference('sup+', [status(thm)], ['49', '50'])).
% 26.43/26.68  thf('52', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('53', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_2 @ X0)),
% 26.43/26.68      inference('sup-', [status(thm)], ['51', '52'])).
% 26.43/26.68  thf('54', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)),
% 26.43/26.68      inference('demod', [status(thm)], ['48', '53'])).
% 26.43/26.68  thf('55', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('56', plain,
% 26.43/26.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 26.43/26.68         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 26.43/26.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 26.43/26.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 26.43/26.68  thf('57', plain,
% 26.43/26.68      (((k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['55', '56'])).
% 26.43/26.68  thf('58', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('demod', [status(thm)], ['45', '54', '57'])).
% 26.43/26.68  thf(d5_funct_1, axiom,
% 26.43/26.68    (![A:$i]:
% 26.43/26.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 26.43/26.68       ( ![B:$i]:
% 26.43/26.68         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 26.43/26.68           ( ![C:$i]:
% 26.43/26.68             ( ( r2_hidden @ C @ B ) <=>
% 26.43/26.68               ( ?[D:$i]:
% 26.43/26.68                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 26.43/26.68                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 26.43/26.68  thf('59', plain,
% 26.43/26.68      (![X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 26.43/26.68         (((X14) != (k2_relat_1 @ X12))
% 26.43/26.68          | (r2_hidden @ X16 @ X14)
% 26.43/26.68          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 26.43/26.68          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 26.43/26.68          | ~ (v1_funct_1 @ X12)
% 26.43/26.68          | ~ (v1_relat_1 @ X12))),
% 26.43/26.68      inference('cnf', [status(esa)], [d5_funct_1])).
% 26.43/26.68  thf('60', plain,
% 26.43/26.68      (![X12 : $i, X17 : $i]:
% 26.43/26.68         (~ (v1_relat_1 @ X12)
% 26.43/26.68          | ~ (v1_funct_1 @ X12)
% 26.43/26.68          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 26.43/26.68          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 26.43/26.68      inference('simplify', [status(thm)], ['59'])).
% 26.43/26.68  thf('61', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (~ (r2_hidden @ X0 @ sk_B)
% 26.43/26.68          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 26.43/26.68          | ~ (v1_funct_1 @ sk_D_2)
% 26.43/26.68          | ~ (v1_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['58', '60'])).
% 26.43/26.68  thf('62', plain, ((v1_funct_1 @ sk_D_2)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('63', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(cc2_relat_1, axiom,
% 26.43/26.68    (![A:$i]:
% 26.43/26.68     ( ( v1_relat_1 @ A ) =>
% 26.43/26.68       ( ![B:$i]:
% 26.43/26.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 26.43/26.68  thf('64', plain,
% 26.43/26.68      (![X7 : $i, X8 : $i]:
% 26.43/26.68         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 26.43/26.68          | (v1_relat_1 @ X7)
% 26.43/26.68          | ~ (v1_relat_1 @ X8))),
% 26.43/26.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 26.43/26.68  thf('65', plain,
% 26.43/26.68      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)) | (v1_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['63', '64'])).
% 26.43/26.68  thf(fc6_relat_1, axiom,
% 26.43/26.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 26.43/26.68  thf('66', plain,
% 26.43/26.68      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 26.43/26.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 26.43/26.68  thf('67', plain, ((v1_relat_1 @ sk_D_2)),
% 26.43/26.68      inference('demod', [status(thm)], ['65', '66'])).
% 26.43/26.68  thf('68', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (~ (r2_hidden @ X0 @ sk_B)
% 26.43/26.68          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 26.43/26.68      inference('demod', [status(thm)], ['61', '62', '67'])).
% 26.43/26.68  thf('69', plain,
% 26.43/26.68      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k2_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['42', '68'])).
% 26.43/26.68  thf('70', plain,
% 26.43/26.68      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 26.43/26.68        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf(d3_tarski, axiom,
% 26.43/26.68    (![A:$i,B:$i]:
% 26.43/26.68     ( ( r1_tarski @ A @ B ) <=>
% 26.43/26.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 26.43/26.68  thf('71', plain,
% 26.43/26.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.43/26.68         (~ (r2_hidden @ X0 @ X1)
% 26.43/26.68          | (r2_hidden @ X0 @ X2)
% 26.43/26.68          | ~ (r1_tarski @ X1 @ X2))),
% 26.43/26.68      inference('cnf', [status(esa)], [d3_tarski])).
% 26.43/26.68  thf('72', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 26.43/26.68          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 26.43/26.68      inference('sup-', [status(thm)], ['70', '71'])).
% 26.43/26.68  thf('73', plain,
% 26.43/26.68      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 26.43/26.68      inference('sup-', [status(thm)], ['1', '2'])).
% 26.43/26.68  thf('74', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 26.43/26.68          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 26.43/26.68      inference('demod', [status(thm)], ['72', '73'])).
% 26.43/26.68  thf('75', plain,
% 26.43/26.68      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 26.43/26.68      inference('sup-', [status(thm)], ['7', '8'])).
% 26.43/26.68  thf('76', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 26.43/26.68          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 26.43/26.68      inference('demod', [status(thm)], ['74', '75'])).
% 26.43/26.68  thf('77', plain,
% 26.43/26.68      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 26.43/26.68      inference('sup-', [status(thm)], ['69', '76'])).
% 26.43/26.68  thf(d8_partfun1, axiom,
% 26.43/26.68    (![A:$i,B:$i]:
% 26.43/26.68     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 26.43/26.68       ( ![C:$i]:
% 26.43/26.68         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 26.43/26.68           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 26.43/26.68  thf('78', plain,
% 26.43/26.68      (![X35 : $i, X36 : $i, X37 : $i]:
% 26.43/26.68         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 26.43/26.68          | ((k7_partfun1 @ X37 @ X36 @ X35) = (k1_funct_1 @ X36 @ X35))
% 26.43/26.68          | ~ (v1_funct_1 @ X36)
% 26.43/26.68          | ~ (v5_relat_1 @ X36 @ X37)
% 26.43/26.68          | ~ (v1_relat_1 @ X36))),
% 26.43/26.68      inference('cnf', [status(esa)], [d8_partfun1])).
% 26.43/26.68  thf('79', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (~ (v1_relat_1 @ sk_E)
% 26.43/26.68          | ~ (v5_relat_1 @ sk_E @ X0)
% 26.43/26.68          | ~ (v1_funct_1 @ sk_E)
% 26.43/26.68          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 26.43/26.68              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 26.43/26.68      inference('sup-', [status(thm)], ['77', '78'])).
% 26.43/26.68  thf('80', plain,
% 26.43/26.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('81', plain,
% 26.43/26.68      (![X7 : $i, X8 : $i]:
% 26.43/26.68         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 26.43/26.68          | (v1_relat_1 @ X7)
% 26.43/26.68          | ~ (v1_relat_1 @ X8))),
% 26.43/26.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 26.43/26.68  thf('82', plain,
% 26.43/26.68      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 26.43/26.68      inference('sup-', [status(thm)], ['80', '81'])).
% 26.43/26.68  thf('83', plain,
% 26.43/26.68      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 26.43/26.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 26.43/26.68  thf('84', plain, ((v1_relat_1 @ sk_E)),
% 26.43/26.68      inference('demod', [status(thm)], ['82', '83'])).
% 26.43/26.68  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 26.43/26.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.43/26.68  thf('86', plain,
% 26.43/26.68      (![X0 : $i]:
% 26.43/26.68         (~ (v5_relat_1 @ sk_E @ X0)
% 26.43/26.68          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 26.43/26.68              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 26.43/26.68      inference('demod', [status(thm)], ['79', '84', '85'])).
% 26.43/26.68  thf('87', plain,
% 26.43/26.68      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 26.43/26.68         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 26.43/26.68      inference('sup-', [status(thm)], ['30', '86'])).
% 26.43/26.68  thf('88', plain,
% 26.43/26.68      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 26.43/26.68         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 26.43/26.68      inference('demod', [status(thm)], ['27', '87'])).
% 26.43/26.68  thf('89', plain, ($false),
% 26.43/26.68      inference('simplify_reflect-', [status(thm)], ['26', '88'])).
% 26.43/26.68  
% 26.43/26.68  % SZS output end Refutation
% 26.43/26.68  
% 26.43/26.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
