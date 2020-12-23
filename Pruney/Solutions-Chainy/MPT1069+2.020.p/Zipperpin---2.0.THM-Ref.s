%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7vnh0AwnLK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:04 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 267 expanded)
%              Number of leaves         :   45 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          : 1311 (5754 expanded)
%              Number of equality atoms :   59 ( 232 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['6','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_1 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( zip_tseitin_0 @ X41 @ X42 @ X40 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X40 @ X39 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ sk_D @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_2 @ X34 @ X36 @ X35 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ ( k1_relat_1 @ sk_E ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','38'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k7_partfun1 @ X23 @ X22 @ X21 )
        = ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['41','44','45'])).

thf('47',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','46'])).

thf('48',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ X25 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28 ) @ X27 )
        = ( k1_funct_1 @ X28 @ ( k1_funct_1 @ X24 @ X27 ) ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X25 @ X26 @ X24 ) @ ( k1_relset_1 @ X26 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['49','65'])).

thf('67',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['48','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['47','67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( v1_partfun1 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ~ ( v1_partfun1 @ sk_D @ sk_B )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['12','13'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['71','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('90',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7vnh0AwnLK
% 0.13/0.36  % Computer   : n005.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:52:18 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.58/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.83  % Solved by: fo/fo7.sh
% 0.58/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.83  % done 784 iterations in 0.357s
% 0.58/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.83  % SZS output start Refutation
% 0.58/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.58/0.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.83  thf(sk_F_type, type, sk_F: $i).
% 0.58/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.83  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.58/0.83  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.58/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.83  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.58/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.83  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.83  thf(t186_funct_2, conjecture,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.58/0.83       ( ![D:$i]:
% 0.58/0.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.58/0.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.83           ( ![E:$i]:
% 0.58/0.83             ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.83                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.58/0.83               ( ![F:$i]:
% 0.58/0.83                 ( ( m1_subset_1 @ F @ B ) =>
% 0.58/0.83                   ( ( r1_tarski @
% 0.58/0.83                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.58/0.83                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.58/0.83                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.83                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.58/0.83                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.83        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.58/0.83          ( ![D:$i]:
% 0.58/0.83            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.58/0.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.83              ( ![E:$i]:
% 0.58/0.83                ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.83                    ( m1_subset_1 @
% 0.58/0.83                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.58/0.83                  ( ![F:$i]:
% 0.58/0.83                    ( ( m1_subset_1 @ F @ B ) =>
% 0.58/0.83                      ( ( r1_tarski @
% 0.58/0.83                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.58/0.83                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.58/0.83                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.83                          ( ( k1_funct_1 @
% 0.58/0.83                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.58/0.83                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.83    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.58/0.83  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('1', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(cc2_relset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.83  thf('2', plain,
% 0.58/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.83         ((v5_relat_1 @ X9 @ X11)
% 0.58/0.83          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.83  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.58/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.83  thf('4', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(t2_subset, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ A @ B ) =>
% 0.58/0.83       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.83  thf('5', plain,
% 0.58/0.83      (![X4 : $i, X5 : $i]:
% 0.58/0.83         ((r2_hidden @ X4 @ X5)
% 0.58/0.83          | (v1_xboole_0 @ X5)
% 0.58/0.83          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.58/0.83      inference('cnf', [status(esa)], [t2_subset])).
% 0.58/0.83  thf('6', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.83  thf(l13_xboole_0, axiom,
% 0.58/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.83  thf('7', plain,
% 0.58/0.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.83  thf('8', plain,
% 0.58/0.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.58/0.83  thf('9', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.83      inference('sup+', [status(thm)], ['7', '8'])).
% 0.58/0.83  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('11', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((X0) != (k1_xboole_0))
% 0.58/0.83          | ~ (v1_xboole_0 @ X0)
% 0.58/0.83          | ~ (v1_xboole_0 @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.83  thf('12', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.58/0.83      inference('simplify', [status(thm)], ['11'])).
% 0.58/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.58/0.83  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.83  thf('14', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.58/0.83      inference('simplify_reflect+', [status(thm)], ['12', '13'])).
% 0.58/0.83  thf('15', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.58/0.83      inference('clc', [status(thm)], ['6', '14'])).
% 0.58/0.83  thf('16', plain,
% 0.58/0.83      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.83        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('17', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.83  thf('18', plain,
% 0.58/0.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.83         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.58/0.83          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.58/0.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.83  thf('19', plain,
% 0.58/0.83      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.58/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.83  thf('20', plain,
% 0.58/0.83      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.58/0.83      inference('demod', [status(thm)], ['16', '19'])).
% 0.58/0.83  thf('21', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(t8_funct_2, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.83     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.83         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.58/0.83       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.58/0.83         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.58/0.83             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.58/0.83           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.58/0.83  thf(zf_stmt_2, axiom,
% 0.58/0.83    (![B:$i,A:$i]:
% 0.58/0.83     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.58/0.83       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.58/0.83  thf(zf_stmt_4, axiom,
% 0.58/0.83    (![D:$i,C:$i,A:$i]:
% 0.58/0.83     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.58/0.83       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.58/0.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_5, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.83     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.83       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.58/0.83         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.58/0.83  thf('22', plain,
% 0.58/0.83      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.58/0.83         ((zip_tseitin_1 @ X39 @ X40)
% 0.58/0.83          | ~ (v1_funct_1 @ X41)
% 0.58/0.83          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.58/0.83          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.58/0.83          | (zip_tseitin_0 @ X41 @ X42 @ X40)
% 0.58/0.83          | ~ (r1_tarski @ (k2_relset_1 @ X40 @ X39 @ X41) @ X42))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.83  thf('23', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.58/0.83          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.58/0.83          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.58/0.83          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.83          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.83  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('26', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ X0)
% 0.58/0.83          | (zip_tseitin_0 @ sk_D @ X0 @ sk_B)
% 0.58/0.83          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.58/0.83  thf('27', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['20', '26'])).
% 0.58/0.83  thf('28', plain,
% 0.58/0.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.83         ((v1_funct_2 @ X34 @ X36 @ X35) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.83  thf('29', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['27', '28'])).
% 0.58/0.83  thf('30', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | (zip_tseitin_0 @ sk_D @ (k1_relat_1 @ sk_E) @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['20', '26'])).
% 0.58/0.83  thf('31', plain,
% 0.58/0.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.83         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.58/0.83          | ~ (zip_tseitin_0 @ X34 @ X35 @ X36))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.83  thf('32', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | (m1_subset_1 @ sk_D @ 
% 0.58/0.83           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.83  thf(t7_funct_2, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.83     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.83       ( ( r2_hidden @ C @ A ) =>
% 0.58/0.83         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.83           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.58/0.83  thf('33', plain,
% 0.58/0.83      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X30 @ X31)
% 0.58/0.83          | ((X32) = (k1_xboole_0))
% 0.58/0.83          | ~ (v1_funct_1 @ X33)
% 0.58/0.83          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.58/0.83          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.58/0.83          | (r2_hidden @ (k1_funct_1 @ X33 @ X30) @ X32))),
% 0.58/0.83      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.58/0.83  thf('34', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.58/0.83          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.58/0.83          | ~ (v1_funct_1 @ sk_D)
% 0.58/0.83          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.83  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('36', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.58/0.83          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.58/0.83          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['34', '35'])).
% 0.58/0.83  thf('37', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83          | ~ (r2_hidden @ X0 @ sk_B)
% 0.58/0.83          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.58/0.83          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['29', '36'])).
% 0.58/0.83  thf('38', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.58/0.83          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83          | ~ (r2_hidden @ X0 @ sk_B)
% 0.58/0.83          | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.83  thf('39', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['15', '38'])).
% 0.58/0.83  thf(d8_partfun1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.83       ( ![C:$i]:
% 0.58/0.83         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.58/0.83           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.58/0.83  thf('40', plain,
% 0.58/0.83      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.83         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.58/0.83          | ((k7_partfun1 @ X23 @ X22 @ X21) = (k1_funct_1 @ X22 @ X21))
% 0.58/0.83          | ~ (v1_funct_1 @ X22)
% 0.58/0.83          | ~ (v5_relat_1 @ X22 @ X23)
% 0.58/0.83          | ~ (v1_relat_1 @ X22))),
% 0.58/0.83      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.58/0.83  thf('41', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83          | ~ (v1_relat_1 @ sk_E)
% 0.58/0.83          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.58/0.83          | ~ (v1_funct_1 @ sk_E)
% 0.58/0.83          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.58/0.83              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.83  thf('42', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(cc1_relset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83       ( v1_relat_1 @ C ) ))).
% 0.58/0.83  thf('43', plain,
% 0.58/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.83         ((v1_relat_1 @ X6)
% 0.58/0.83          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.58/0.83      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.83  thf('44', plain, ((v1_relat_1 @ sk_E)),
% 0.58/0.83      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.83  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('46', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83          | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.58/0.83          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.58/0.83              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.58/0.83      inference('demod', [status(thm)], ['41', '44', '45'])).
% 0.58/0.83  thf('47', plain,
% 0.58/0.83      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.58/0.83          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.58/0.83        | (zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['3', '46'])).
% 0.58/0.83  thf('48', plain,
% 0.58/0.83      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.58/0.83         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('49', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('50', plain,
% 0.58/0.83      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.58/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.83  thf('51', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(t185_funct_2, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.58/0.83       ( ![D:$i]:
% 0.58/0.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.58/0.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.58/0.83           ( ![E:$i]:
% 0.58/0.83             ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.83                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.58/0.83               ( ![F:$i]:
% 0.58/0.83                 ( ( m1_subset_1 @ F @ B ) =>
% 0.58/0.83                   ( ( r1_tarski @
% 0.58/0.83                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.58/0.83                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.58/0.83                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.83                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.58/0.83                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.83  thf('52', plain,
% 0.58/0.83      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.83         (~ (v1_funct_1 @ X24)
% 0.58/0.83          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.58/0.83          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.58/0.83          | ~ (m1_subset_1 @ X27 @ X25)
% 0.58/0.83          | ((k1_funct_1 @ (k8_funct_2 @ X25 @ X26 @ X29 @ X24 @ X28) @ X27)
% 0.58/0.83              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X24 @ X27)))
% 0.58/0.83          | ((X25) = (k1_xboole_0))
% 0.58/0.83          | ~ (r1_tarski @ (k2_relset_1 @ X25 @ X26 @ X24) @ 
% 0.58/0.83               (k1_relset_1 @ X26 @ X29 @ X28))
% 0.58/0.83          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X29)))
% 0.58/0.83          | ~ (v1_funct_1 @ X28)
% 0.58/0.83          | (v1_xboole_0 @ X26))),
% 0.58/0.83      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.58/0.83  thf('53', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         ((v1_xboole_0 @ sk_C)
% 0.58/0.83          | ~ (v1_funct_1 @ X0)
% 0.58/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.58/0.83          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.83               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.58/0.83          | ((sk_B) = (k1_xboole_0))
% 0.58/0.83          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.58/0.83              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.58/0.83          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.58/0.83          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.58/0.83          | ~ (v1_funct_1 @ sk_D))),
% 0.58/0.83      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.83  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('56', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         ((v1_xboole_0 @ sk_C)
% 0.58/0.83          | ~ (v1_funct_1 @ X0)
% 0.58/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.58/0.83          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.83               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.58/0.83          | ((sk_B) = (k1_xboole_0))
% 0.58/0.83          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.58/0.83              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.58/0.83          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.58/0.83  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('58', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.83         ((v1_xboole_0 @ sk_C)
% 0.58/0.83          | ~ (v1_funct_1 @ X0)
% 0.58/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.58/0.83          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.83               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.58/0.83          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.58/0.83              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.58/0.83          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.58/0.83      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.58/0.83  thf('59', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.58/0.83             (k1_relat_1 @ sk_E))
% 0.58/0.83          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.83          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.58/0.83              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.58/0.83          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.58/0.83          | ~ (v1_funct_1 @ sk_E)
% 0.58/0.83          | (v1_xboole_0 @ sk_C))),
% 0.58/0.83      inference('sup-', [status(thm)], ['50', '58'])).
% 0.58/0.83  thf('60', plain,
% 0.58/0.83      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.58/0.83      inference('demod', [status(thm)], ['16', '19'])).
% 0.58/0.83  thf('61', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('62', plain, ((v1_funct_1 @ sk_E)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('63', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.58/0.83          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.58/0.83              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.58/0.83          | (v1_xboole_0 @ sk_C))),
% 0.58/0.83      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.58/0.83  thf('64', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('65', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.58/0.83            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.58/0.83          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.58/0.83      inference('clc', [status(thm)], ['63', '64'])).
% 0.58/0.83  thf('66', plain,
% 0.58/0.83      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.58/0.83         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['49', '65'])).
% 0.58/0.83  thf('67', plain,
% 0.58/0.83      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.58/0.83         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.58/0.83      inference('demod', [status(thm)], ['48', '66'])).
% 0.58/0.83  thf('68', plain,
% 0.58/0.83      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.58/0.83          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.58/0.83        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.58/0.83        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['47', '67'])).
% 0.58/0.83  thf('69', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.58/0.83      inference('simplify', [status(thm)], ['68'])).
% 0.58/0.83  thf('70', plain,
% 0.58/0.83      (![X37 : $i, X38 : $i]:
% 0.58/0.83         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.83  thf('71', plain,
% 0.58/0.83      ((((k1_relat_1 @ sk_E) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.83  thf('72', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | (m1_subset_1 @ sk_D @ 
% 0.58/0.83           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.83  thf(cc2_partfun1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.58/0.83       ( ![C:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.58/0.83  thf('73', plain,
% 0.58/0.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.83         ((v1_xboole_0 @ X15)
% 0.58/0.83          | ~ (v1_xboole_0 @ X16)
% 0.58/0.83          | ~ (v1_partfun1 @ X17 @ X15)
% 0.58/0.83          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.58/0.83      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.58/0.83  thf('74', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | ~ (v1_partfun1 @ sk_D @ sk_B)
% 0.58/0.83        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.58/0.83        | (v1_xboole_0 @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['72', '73'])).
% 0.58/0.83  thf('75', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(cc5_funct_2, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.58/0.83       ( ![C:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.83           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.58/0.83             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.58/0.83  thf('76', plain,
% 0.58/0.83      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.58/0.83          | (v1_partfun1 @ X18 @ X19)
% 0.58/0.83          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.58/0.83          | ~ (v1_funct_1 @ X18)
% 0.58/0.83          | (v1_xboole_0 @ X20))),
% 0.58/0.83      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.58/0.83  thf('77', plain,
% 0.58/0.83      (((v1_xboole_0 @ sk_C)
% 0.58/0.83        | ~ (v1_funct_1 @ sk_D)
% 0.58/0.83        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.58/0.83        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['75', '76'])).
% 0.58/0.83  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('80', plain, (((v1_xboole_0 @ sk_C) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.58/0.83  thf('81', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('82', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.58/0.83      inference('clc', [status(thm)], ['80', '81'])).
% 0.58/0.83  thf('83', plain,
% 0.58/0.83      (((zip_tseitin_1 @ sk_C @ sk_B)
% 0.58/0.83        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))
% 0.58/0.83        | (v1_xboole_0 @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['74', '82'])).
% 0.58/0.83  thf('84', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.58/0.83      inference('simplify_reflect+', [status(thm)], ['12', '13'])).
% 0.58/0.83  thf('85', plain,
% 0.58/0.83      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_E)) | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('clc', [status(thm)], ['83', '84'])).
% 0.58/0.83  thf('86', plain,
% 0.58/0.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.83        | ((sk_C) = (k1_xboole_0))
% 0.58/0.83        | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('sup-', [status(thm)], ['71', '85'])).
% 0.58/0.83  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.83  thf('88', plain,
% 0.58/0.83      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B))),
% 0.58/0.83      inference('demod', [status(thm)], ['86', '87'])).
% 0.58/0.83  thf('89', plain,
% 0.58/0.83      (![X37 : $i, X38 : $i]:
% 0.58/0.83         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.83  thf('90', plain, (((sk_C) = (k1_xboole_0))),
% 0.58/0.83      inference('clc', [status(thm)], ['88', '89'])).
% 0.58/0.83  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.58/0.83  thf('92', plain, ($false),
% 0.58/0.83      inference('demod', [status(thm)], ['0', '90', '91'])).
% 0.58/0.83  
% 0.58/0.83  % SZS output end Refutation
% 0.58/0.83  
% 0.58/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
