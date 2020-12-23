%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A03N6kgVCK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:05 EST 2020

% Result     : Theorem 24.73s
% Output     : Refutation 24.73s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 579 expanded)
%              Number of leaves         :   50 ( 192 expanded)
%              Depth                    :   20
%              Number of atoms          : 1595 (11807 expanded)
%              Number of equality atoms :   87 ( 517 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_funct_2 @ X33 @ X31 @ X32 @ X34 @ X30 )
        = ( k1_partfun1 @ X33 @ X31 @ X31 @ X32 @ X34 @ X30 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X33 @ X31 @ X34 ) @ ( k1_relset_1 @ X31 @ X32 @ X30 ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_2 ) ) )
      | ( sk_C_2 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_2 @ X0 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_2 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_2 @ sk_C_2 @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_2 ) ) )
      | ( sk_C_2 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_2 @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_2 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_2 @ sk_C_2 @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['6','9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) )
    | ( ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C_2 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C_2 @ X2 @ X1 @ sk_D_2 @ X0 )
        = ( k5_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C_2 @ X2 @ X1 @ sk_D_2 @ X0 )
        = ( k5_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C_2 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E )
      = ( k5_relat_1 @ sk_D_2 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C_2 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E )
    = ( k5_relat_1 @ sk_D_2 @ sk_E ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E )
      = ( k5_relat_1 @ sk_D_2 @ sk_E ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','17','26','27','28','29'])).

thf('31',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['37','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['47','56','59'])).

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

thf('61',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['63','64','67'])).

thf('69',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['44','68'])).

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
    inference('sup-',[status(thm)],['7','8'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ X44 ) )
      | ( ( k7_partfun1 @ X45 @ X44 @ X43 )
        = ( k1_funct_1 @ X44 @ X43 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v5_relat_1 @ X44 @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('82',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['79','82','83'])).

thf('85',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['34','84'])).

thf('86',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['31','85'])).

thf('87',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['37','43'])).

thf('88',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['47','56','59'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k1_funct_1 @ X15 @ ( k1_funct_1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('92',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('96',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('97',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) @ ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('100',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) @ ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['94','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('104',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('106',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( sk_D_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) @ sk_E ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('110',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( sk_D_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('112',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) @ ( k2_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('113',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('114',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( sk_D_1 @ ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) @ sk_E ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('117',plain,
    ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( sk_D_1 @ ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( sk_D_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) @ sk_E ) ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['111','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('121',plain,
    ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( sk_D_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) ),
    inference('sup+',[status(thm)],['110','121'])).

thf('123',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['86','122'])).

thf('124',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D_2 @ sk_E ) @ sk_F ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','123'])).

thf('125',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A03N6kgVCK
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 24.73/25.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.73/25.01  % Solved by: fo/fo7.sh
% 24.73/25.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.73/25.01  % done 4731 iterations in 24.543s
% 24.73/25.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.73/25.01  % SZS output start Refutation
% 24.73/25.01  thf(sk_E_type, type, sk_E: $i).
% 24.73/25.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 24.73/25.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 24.73/25.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 24.73/25.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 24.73/25.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 24.73/25.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 24.73/25.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.73/25.01  thf(sk_C_2_type, type, sk_C_2: $i).
% 24.73/25.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 24.73/25.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 24.73/25.01  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 24.73/25.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 24.73/25.01  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 24.73/25.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 24.73/25.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 24.73/25.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 24.73/25.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 24.73/25.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 24.73/25.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 24.73/25.01  thf(sk_D_2_type, type, sk_D_2: $i).
% 24.73/25.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.73/25.01  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 24.73/25.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 24.73/25.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 24.73/25.01  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 24.73/25.01  thf(sk_B_type, type, sk_B: $i).
% 24.73/25.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 24.73/25.01  thf(sk_A_type, type, sk_A: $i).
% 24.73/25.01  thf(sk_F_type, type, sk_F: $i).
% 24.73/25.01  thf(t186_funct_2, conjecture,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( ~( v1_xboole_0 @ C ) ) =>
% 24.73/25.01       ( ![D:$i]:
% 24.73/25.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 24.73/25.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 24.73/25.01           ( ![E:$i]:
% 24.73/25.01             ( ( ( v1_funct_1 @ E ) & 
% 24.73/25.01                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 24.73/25.01               ( ![F:$i]:
% 24.73/25.01                 ( ( m1_subset_1 @ F @ B ) =>
% 24.73/25.01                   ( ( r1_tarski @
% 24.73/25.01                       ( k2_relset_1 @ B @ C @ D ) @ 
% 24.73/25.01                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 24.73/25.01                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 24.73/25.01                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 24.73/25.01                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 24.73/25.01  thf(zf_stmt_0, negated_conjecture,
% 24.73/25.01    (~( ![A:$i,B:$i,C:$i]:
% 24.73/25.01        ( ( ~( v1_xboole_0 @ C ) ) =>
% 24.73/25.01          ( ![D:$i]:
% 24.73/25.01            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 24.73/25.01                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 24.73/25.01              ( ![E:$i]:
% 24.73/25.01                ( ( ( v1_funct_1 @ E ) & 
% 24.73/25.01                    ( m1_subset_1 @
% 24.73/25.01                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 24.73/25.01                  ( ![F:$i]:
% 24.73/25.01                    ( ( m1_subset_1 @ F @ B ) =>
% 24.73/25.01                      ( ( r1_tarski @
% 24.73/25.01                          ( k2_relset_1 @ B @ C @ D ) @ 
% 24.73/25.01                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 24.73/25.01                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 24.73/25.01                          ( ( k1_funct_1 @
% 24.73/25.01                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 24.73/25.01                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 24.73/25.01    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 24.73/25.01  thf('0', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('1', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(redefinition_k2_relset_1, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.73/25.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 24.73/25.01  thf('2', plain,
% 24.73/25.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 24.73/25.01         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 24.73/25.01          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 24.73/25.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 24.73/25.01  thf('3', plain,
% 24.73/25.01      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['1', '2'])).
% 24.73/25.01  thf('4', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(d12_funct_2, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i,D:$i]:
% 24.73/25.01     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 24.73/25.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 24.73/25.01       ( ![E:$i]:
% 24.73/25.01         ( ( ( v1_funct_1 @ E ) & 
% 24.73/25.01             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 24.73/25.01           ( ( r1_tarski @
% 24.73/25.01               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 24.73/25.01             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 24.73/25.01               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 24.73/25.01                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 24.73/25.01  thf('5', plain,
% 24.73/25.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 24.73/25.01         (~ (v1_funct_1 @ X30)
% 24.73/25.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 24.73/25.01          | ((k8_funct_2 @ X33 @ X31 @ X32 @ X34 @ X30)
% 24.73/25.01              = (k1_partfun1 @ X33 @ X31 @ X31 @ X32 @ X34 @ X30))
% 24.73/25.01          | ~ (r1_tarski @ (k2_relset_1 @ X33 @ X31 @ X34) @ 
% 24.73/25.01               (k1_relset_1 @ X31 @ X32 @ X30))
% 24.73/25.01          | ((X31) = (k1_xboole_0))
% 24.73/25.01          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 24.73/25.01          | ~ (v1_funct_2 @ X34 @ X33 @ X31)
% 24.73/25.01          | ~ (v1_funct_1 @ X34))),
% 24.73/25.01      inference('cnf', [status(esa)], [d12_funct_2])).
% 24.73/25.01  thf('6', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i]:
% 24.73/25.01         (~ (v1_funct_1 @ X0)
% 24.73/25.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_2)
% 24.73/25.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_2)))
% 24.73/25.01          | ((sk_C_2) = (k1_xboole_0))
% 24.73/25.01          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_2 @ X0) @ 
% 24.73/25.01               (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 24.73/25.01          | ((k8_funct_2 @ X1 @ sk_C_2 @ sk_A @ X0 @ sk_E)
% 24.73/25.01              = (k1_partfun1 @ X1 @ sk_C_2 @ sk_C_2 @ sk_A @ X0 @ sk_E))
% 24.73/25.01          | ~ (v1_funct_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['4', '5'])).
% 24.73/25.01  thf('7', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(redefinition_k1_relset_1, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.73/25.01       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 24.73/25.01  thf('8', plain,
% 24.73/25.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 24.73/25.01         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 24.73/25.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 24.73/25.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 24.73/25.01  thf('9', plain,
% 24.73/25.01      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['7', '8'])).
% 24.73/25.01  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('11', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i]:
% 24.73/25.01         (~ (v1_funct_1 @ X0)
% 24.73/25.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_2)
% 24.73/25.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_2)))
% 24.73/25.01          | ((sk_C_2) = (k1_xboole_0))
% 24.73/25.01          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_2 @ X0) @ 
% 24.73/25.01               (k1_relat_1 @ sk_E))
% 24.73/25.01          | ((k8_funct_2 @ X1 @ sk_C_2 @ sk_A @ X0 @ sk_E)
% 24.73/25.01              = (k1_partfun1 @ X1 @ sk_C_2 @ sk_C_2 @ sk_A @ X0 @ sk_E)))),
% 24.73/25.01      inference('demod', [status(thm)], ['6', '9', '10'])).
% 24.73/25.01  thf('12', plain,
% 24.73/25.01      ((~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 24.73/25.01        | ((k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E)
% 24.73/25.01            = (k1_partfun1 @ sk_B @ sk_C_2 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E))
% 24.73/25.01        | ((sk_C_2) = (k1_xboole_0))
% 24.73/25.01        | ~ (m1_subset_1 @ sk_D_2 @ 
% 24.73/25.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))
% 24.73/25.01        | ~ (v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)
% 24.73/25.01        | ~ (v1_funct_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['3', '11'])).
% 24.73/25.01  thf('13', plain,
% 24.73/25.01      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 24.73/25.01        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('14', plain,
% 24.73/25.01      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['7', '8'])).
% 24.73/25.01  thf('15', plain,
% 24.73/25.01      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 24.73/25.01        (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('demod', [status(thm)], ['13', '14'])).
% 24.73/25.01  thf('16', plain,
% 24.73/25.01      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['1', '2'])).
% 24.73/25.01  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('demod', [status(thm)], ['15', '16'])).
% 24.73/25.01  thf('18', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('19', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(redefinition_k1_partfun1, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 24.73/25.01     ( ( ( v1_funct_1 @ E ) & 
% 24.73/25.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 24.73/25.01         ( v1_funct_1 @ F ) & 
% 24.73/25.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 24.73/25.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 24.73/25.01  thf('20', plain,
% 24.73/25.01      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 24.73/25.01         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 24.73/25.01          | ~ (v1_funct_1 @ X46)
% 24.73/25.01          | ~ (v1_funct_1 @ X49)
% 24.73/25.01          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 24.73/25.01          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 24.73/25.01              = (k5_relat_1 @ X46 @ X49)))),
% 24.73/25.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 24.73/25.01  thf('21', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.73/25.01         (((k1_partfun1 @ sk_B @ sk_C_2 @ X2 @ X1 @ sk_D_2 @ X0)
% 24.73/25.01            = (k5_relat_1 @ sk_D_2 @ X0))
% 24.73/25.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 24.73/25.01          | ~ (v1_funct_1 @ X0)
% 24.73/25.01          | ~ (v1_funct_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['19', '20'])).
% 24.73/25.01  thf('22', plain, ((v1_funct_1 @ sk_D_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('23', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.73/25.01         (((k1_partfun1 @ sk_B @ sk_C_2 @ X2 @ X1 @ sk_D_2 @ X0)
% 24.73/25.01            = (k5_relat_1 @ sk_D_2 @ X0))
% 24.73/25.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 24.73/25.01          | ~ (v1_funct_1 @ X0))),
% 24.73/25.01      inference('demod', [status(thm)], ['21', '22'])).
% 24.73/25.01  thf('24', plain,
% 24.73/25.01      ((~ (v1_funct_1 @ sk_E)
% 24.73/25.01        | ((k1_partfun1 @ sk_B @ sk_C_2 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E)
% 24.73/25.01            = (k5_relat_1 @ sk_D_2 @ sk_E)))),
% 24.73/25.01      inference('sup-', [status(thm)], ['18', '23'])).
% 24.73/25.01  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('26', plain,
% 24.73/25.01      (((k1_partfun1 @ sk_B @ sk_C_2 @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E)
% 24.73/25.01         = (k5_relat_1 @ sk_D_2 @ sk_E))),
% 24.73/25.01      inference('demod', [status(thm)], ['24', '25'])).
% 24.73/25.01  thf('27', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('28', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('29', plain, ((v1_funct_1 @ sk_D_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('30', plain,
% 24.73/25.01      ((((k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E)
% 24.73/25.01          = (k5_relat_1 @ sk_D_2 @ sk_E))
% 24.73/25.01        | ((sk_C_2) = (k1_xboole_0)))),
% 24.73/25.01      inference('demod', [status(thm)], ['12', '17', '26', '27', '28', '29'])).
% 24.73/25.01  thf('31', plain,
% 24.73/25.01      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 24.73/25.01         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('32', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(cc2_relset_1, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.73/25.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 24.73/25.01  thf('33', plain,
% 24.73/25.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 24.73/25.01         ((v5_relat_1 @ X21 @ X23)
% 24.73/25.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 24.73/25.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 24.73/25.01  thf('34', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 24.73/25.01      inference('sup-', [status(thm)], ['32', '33'])).
% 24.73/25.01  thf('35', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(t2_subset, axiom,
% 24.73/25.01    (![A:$i,B:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ A @ B ) =>
% 24.73/25.01       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 24.73/25.01  thf('36', plain,
% 24.73/25.01      (![X6 : $i, X7 : $i]:
% 24.73/25.01         ((r2_hidden @ X6 @ X7)
% 24.73/25.01          | (v1_xboole_0 @ X7)
% 24.73/25.01          | ~ (m1_subset_1 @ X6 @ X7))),
% 24.73/25.01      inference('cnf', [status(esa)], [t2_subset])).
% 24.73/25.01  thf('37', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 24.73/25.01      inference('sup-', [status(thm)], ['35', '36'])).
% 24.73/25.01  thf(t8_boole, axiom,
% 24.73/25.01    (![A:$i,B:$i]:
% 24.73/25.01     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 24.73/25.01  thf('38', plain,
% 24.73/25.01      (![X4 : $i, X5 : $i]:
% 24.73/25.01         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 24.73/25.01      inference('cnf', [status(esa)], [t8_boole])).
% 24.73/25.01  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('40', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (((X0) != (k1_xboole_0))
% 24.73/25.01          | ~ (v1_xboole_0 @ sk_B)
% 24.73/25.01          | ~ (v1_xboole_0 @ X0))),
% 24.73/25.01      inference('sup-', [status(thm)], ['38', '39'])).
% 24.73/25.01  thf('41', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 24.73/25.01      inference('simplify', [status(thm)], ['40'])).
% 24.73/25.01  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 24.73/25.01  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.73/25.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.73/25.01  thf('43', plain, (~ (v1_xboole_0 @ sk_B)),
% 24.73/25.01      inference('simplify_reflect+', [status(thm)], ['41', '42'])).
% 24.73/25.01  thf('44', plain, ((r2_hidden @ sk_F @ sk_B)),
% 24.73/25.01      inference('clc', [status(thm)], ['37', '43'])).
% 24.73/25.01  thf('45', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(d1_funct_2, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.73/25.01       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 24.73/25.01           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 24.73/25.01             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 24.73/25.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 24.73/25.01           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 24.73/25.01             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 24.73/25.01  thf(zf_stmt_1, axiom,
% 24.73/25.01    (![C:$i,B:$i,A:$i]:
% 24.73/25.01     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 24.73/25.01       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 24.73/25.01  thf('46', plain,
% 24.73/25.01      (![X37 : $i, X38 : $i, X39 : $i]:
% 24.73/25.01         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 24.73/25.01          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 24.73/25.01          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 24.73/25.01  thf('47', plain,
% 24.73/25.01      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 24.73/25.01        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 24.73/25.01      inference('sup-', [status(thm)], ['45', '46'])).
% 24.73/25.01  thf('48', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 24.73/25.01  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 24.73/25.01  thf(zf_stmt_4, axiom,
% 24.73/25.01    (![B:$i,A:$i]:
% 24.73/25.01     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 24.73/25.01       ( zip_tseitin_0 @ B @ A ) ))).
% 24.73/25.01  thf(zf_stmt_5, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.73/25.01       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 24.73/25.01         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 24.73/25.01           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 24.73/25.01             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 24.73/25.01  thf('49', plain,
% 24.73/25.01      (![X40 : $i, X41 : $i, X42 : $i]:
% 24.73/25.01         (~ (zip_tseitin_0 @ X40 @ X41)
% 24.73/25.01          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 24.73/25.01          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 24.73/25.01  thf('50', plain,
% 24.73/25.01      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 24.73/25.01        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B))),
% 24.73/25.01      inference('sup-', [status(thm)], ['48', '49'])).
% 24.73/25.01  thf('51', plain,
% 24.73/25.01      (![X35 : $i, X36 : $i]:
% 24.73/25.01         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_4])).
% 24.73/25.01  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.73/25.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.73/25.01  thf('53', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 24.73/25.01      inference('sup+', [status(thm)], ['51', '52'])).
% 24.73/25.01  thf('54', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('55', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_2 @ X0)),
% 24.73/25.01      inference('sup-', [status(thm)], ['53', '54'])).
% 24.73/25.01  thf('56', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)),
% 24.73/25.01      inference('demod', [status(thm)], ['50', '55'])).
% 24.73/25.01  thf('57', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('58', plain,
% 24.73/25.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 24.73/25.01         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 24.73/25.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 24.73/25.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 24.73/25.01  thf('59', plain,
% 24.73/25.01      (((k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['57', '58'])).
% 24.73/25.01  thf('60', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('demod', [status(thm)], ['47', '56', '59'])).
% 24.73/25.01  thf(d5_funct_1, axiom,
% 24.73/25.01    (![A:$i]:
% 24.73/25.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 24.73/25.01       ( ![B:$i]:
% 24.73/25.01         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 24.73/25.01           ( ![C:$i]:
% 24.73/25.01             ( ( r2_hidden @ C @ B ) <=>
% 24.73/25.01               ( ?[D:$i]:
% 24.73/25.01                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 24.73/25.01                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 24.73/25.01  thf('61', plain,
% 24.73/25.01      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 24.73/25.01         (((X11) != (k2_relat_1 @ X9))
% 24.73/25.01          | (r2_hidden @ X13 @ X11)
% 24.73/25.01          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 24.73/25.01          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 24.73/25.01          | ~ (v1_funct_1 @ X9)
% 24.73/25.01          | ~ (v1_relat_1 @ X9))),
% 24.73/25.01      inference('cnf', [status(esa)], [d5_funct_1])).
% 24.73/25.01  thf('62', plain,
% 24.73/25.01      (![X9 : $i, X14 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X9)
% 24.73/25.01          | ~ (v1_funct_1 @ X9)
% 24.73/25.01          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 24.73/25.01          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 24.73/25.01      inference('simplify', [status(thm)], ['61'])).
% 24.73/25.01  thf('63', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (~ (r2_hidden @ X0 @ sk_B)
% 24.73/25.01          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 24.73/25.01          | ~ (v1_funct_1 @ sk_D_2)
% 24.73/25.01          | ~ (v1_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['60', '62'])).
% 24.73/25.01  thf('64', plain, ((v1_funct_1 @ sk_D_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('65', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(cc1_relset_1, axiom,
% 24.73/25.01    (![A:$i,B:$i,C:$i]:
% 24.73/25.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 24.73/25.01       ( v1_relat_1 @ C ) ))).
% 24.73/25.01  thf('66', plain,
% 24.73/25.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 24.73/25.01         ((v1_relat_1 @ X18)
% 24.73/25.01          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 24.73/25.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 24.73/25.01  thf('67', plain, ((v1_relat_1 @ sk_D_2)),
% 24.73/25.01      inference('sup-', [status(thm)], ['65', '66'])).
% 24.73/25.01  thf('68', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (~ (r2_hidden @ X0 @ sk_B)
% 24.73/25.01          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 24.73/25.01      inference('demod', [status(thm)], ['63', '64', '67'])).
% 24.73/25.01  thf('69', plain,
% 24.73/25.01      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k2_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['44', '68'])).
% 24.73/25.01  thf('70', plain,
% 24.73/25.01      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 24.73/25.01        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf(d3_tarski, axiom,
% 24.73/25.01    (![A:$i,B:$i]:
% 24.73/25.01     ( ( r1_tarski @ A @ B ) <=>
% 24.73/25.01       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 24.73/25.01  thf('71', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.73/25.01         (~ (r2_hidden @ X0 @ X1)
% 24.73/25.01          | (r2_hidden @ X0 @ X2)
% 24.73/25.01          | ~ (r1_tarski @ X1 @ X2))),
% 24.73/25.01      inference('cnf', [status(esa)], [d3_tarski])).
% 24.73/25.01  thf('72', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 24.73/25.01          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 24.73/25.01      inference('sup-', [status(thm)], ['70', '71'])).
% 24.73/25.01  thf('73', plain,
% 24.73/25.01      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['7', '8'])).
% 24.73/25.01  thf('74', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 24.73/25.01          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 24.73/25.01      inference('demod', [status(thm)], ['72', '73'])).
% 24.73/25.01  thf('75', plain,
% 24.73/25.01      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('sup-', [status(thm)], ['1', '2'])).
% 24.73/25.01  thf('76', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 24.73/25.01          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 24.73/25.01      inference('demod', [status(thm)], ['74', '75'])).
% 24.73/25.01  thf('77', plain,
% 24.73/25.01      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['69', '76'])).
% 24.73/25.01  thf(d8_partfun1, axiom,
% 24.73/25.01    (![A:$i,B:$i]:
% 24.73/25.01     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 24.73/25.01       ( ![C:$i]:
% 24.73/25.01         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 24.73/25.01           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 24.73/25.01  thf('78', plain,
% 24.73/25.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 24.73/25.01         (~ (r2_hidden @ X43 @ (k1_relat_1 @ X44))
% 24.73/25.01          | ((k7_partfun1 @ X45 @ X44 @ X43) = (k1_funct_1 @ X44 @ X43))
% 24.73/25.01          | ~ (v1_funct_1 @ X44)
% 24.73/25.01          | ~ (v5_relat_1 @ X44 @ X45)
% 24.73/25.01          | ~ (v1_relat_1 @ X44))),
% 24.73/25.01      inference('cnf', [status(esa)], [d8_partfun1])).
% 24.73/25.01  thf('79', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ sk_E)
% 24.73/25.01          | ~ (v5_relat_1 @ sk_E @ X0)
% 24.73/25.01          | ~ (v1_funct_1 @ sk_E)
% 24.73/25.01          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 24.73/25.01      inference('sup-', [status(thm)], ['77', '78'])).
% 24.73/25.01  thf('80', plain,
% 24.73/25.01      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('81', plain,
% 24.73/25.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 24.73/25.01         ((v1_relat_1 @ X18)
% 24.73/25.01          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 24.73/25.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 24.73/25.01  thf('82', plain, ((v1_relat_1 @ sk_E)),
% 24.73/25.01      inference('sup-', [status(thm)], ['80', '81'])).
% 24.73/25.01  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('84', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (~ (v5_relat_1 @ sk_E @ X0)
% 24.73/25.01          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 24.73/25.01      inference('demod', [status(thm)], ['79', '82', '83'])).
% 24.73/25.01  thf('85', plain,
% 24.73/25.01      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 24.73/25.01      inference('sup-', [status(thm)], ['34', '84'])).
% 24.73/25.01  thf('86', plain,
% 24.73/25.01      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 24.73/25.01         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 24.73/25.01      inference('demod', [status(thm)], ['31', '85'])).
% 24.73/25.01  thf('87', plain, ((r2_hidden @ sk_F @ sk_B)),
% 24.73/25.01      inference('clc', [status(thm)], ['37', '43'])).
% 24.73/25.01  thf('88', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 24.73/25.01      inference('demod', [status(thm)], ['47', '56', '59'])).
% 24.73/25.01  thf(t23_funct_1, axiom,
% 24.73/25.01    (![A:$i,B:$i]:
% 24.73/25.01     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 24.73/25.01       ( ![C:$i]:
% 24.73/25.01         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 24.73/25.01           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 24.73/25.01             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 24.73/25.01               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 24.73/25.01  thf('89', plain,
% 24.73/25.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X15)
% 24.73/25.01          | ~ (v1_funct_1 @ X15)
% 24.73/25.01          | ((k1_funct_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 24.73/25.01              = (k1_funct_1 @ X15 @ (k1_funct_1 @ X16 @ X17)))
% 24.73/25.01          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 24.73/25.01          | ~ (v1_funct_1 @ X16)
% 24.73/25.01          | ~ (v1_relat_1 @ X16))),
% 24.73/25.01      inference('cnf', [status(esa)], [t23_funct_1])).
% 24.73/25.01  thf('90', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i]:
% 24.73/25.01         (~ (r2_hidden @ X0 @ sk_B)
% 24.73/25.01          | ~ (v1_relat_1 @ sk_D_2)
% 24.73/25.01          | ~ (v1_funct_1 @ sk_D_2)
% 24.73/25.01          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ X1) @ X0)
% 24.73/25.01              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D_2 @ X0)))
% 24.73/25.01          | ~ (v1_funct_1 @ X1)
% 24.73/25.01          | ~ (v1_relat_1 @ X1))),
% 24.73/25.01      inference('sup-', [status(thm)], ['88', '89'])).
% 24.73/25.01  thf('91', plain, ((v1_relat_1 @ sk_D_2)),
% 24.73/25.01      inference('sup-', [status(thm)], ['65', '66'])).
% 24.73/25.01  thf('92', plain, ((v1_funct_1 @ sk_D_2)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('93', plain,
% 24.73/25.01      (![X0 : $i, X1 : $i]:
% 24.73/25.01         (~ (r2_hidden @ X0 @ sk_B)
% 24.73/25.01          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ X1) @ X0)
% 24.73/25.01              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D_2 @ X0)))
% 24.73/25.01          | ~ (v1_funct_1 @ X1)
% 24.73/25.01          | ~ (v1_relat_1 @ X1))),
% 24.73/25.01      inference('demod', [status(thm)], ['90', '91', '92'])).
% 24.73/25.01  thf('94', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X0)
% 24.73/25.01          | ~ (v1_funct_1 @ X0)
% 24.73/25.01          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ X0) @ sk_F)
% 24.73/25.01              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 24.73/25.01      inference('sup-', [status(thm)], ['87', '93'])).
% 24.73/25.01  thf('95', plain,
% 24.73/25.01      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['69', '76'])).
% 24.73/25.01  thf('96', plain,
% 24.73/25.01      (![X9 : $i, X14 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X9)
% 24.73/25.01          | ~ (v1_funct_1 @ X9)
% 24.73/25.01          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 24.73/25.01          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 24.73/25.01      inference('simplify', [status(thm)], ['61'])).
% 24.73/25.01  thf('97', plain,
% 24.73/25.01      (((r2_hidden @ (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)) @ 
% 24.73/25.01         (k2_relat_1 @ sk_E))
% 24.73/25.01        | ~ (v1_funct_1 @ sk_E)
% 24.73/25.01        | ~ (v1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['95', '96'])).
% 24.73/25.01  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('99', plain, ((v1_relat_1 @ sk_E)),
% 24.73/25.01      inference('sup-', [status(thm)], ['80', '81'])).
% 24.73/25.01  thf('100', plain,
% 24.73/25.01      ((r2_hidden @ (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)) @ 
% 24.73/25.01        (k2_relat_1 @ sk_E))),
% 24.73/25.01      inference('demod', [status(thm)], ['97', '98', '99'])).
% 24.73/25.01  thf('101', plain,
% 24.73/25.01      (((r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F) @ 
% 24.73/25.01         (k2_relat_1 @ sk_E))
% 24.73/25.01        | ~ (v1_funct_1 @ sk_E)
% 24.73/25.01        | ~ (v1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup+', [status(thm)], ['94', '100'])).
% 24.73/25.01  thf('102', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('103', plain, ((v1_relat_1 @ sk_E)),
% 24.73/25.01      inference('sup-', [status(thm)], ['80', '81'])).
% 24.73/25.01  thf('104', plain,
% 24.73/25.01      ((r2_hidden @ (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F) @ 
% 24.73/25.01        (k2_relat_1 @ sk_E))),
% 24.73/25.01      inference('demod', [status(thm)], ['101', '102', '103'])).
% 24.73/25.01  thf('105', plain,
% 24.73/25.01      (![X9 : $i, X11 : $i, X12 : $i]:
% 24.73/25.01         (((X11) != (k2_relat_1 @ X9))
% 24.73/25.01          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 24.73/25.01          | ~ (r2_hidden @ X12 @ X11)
% 24.73/25.01          | ~ (v1_funct_1 @ X9)
% 24.73/25.01          | ~ (v1_relat_1 @ X9))),
% 24.73/25.01      inference('cnf', [status(esa)], [d5_funct_1])).
% 24.73/25.01  thf('106', plain,
% 24.73/25.01      (![X9 : $i, X12 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X9)
% 24.73/25.01          | ~ (v1_funct_1 @ X9)
% 24.73/25.01          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 24.73/25.01          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 24.73/25.01      inference('simplify', [status(thm)], ['105'])).
% 24.73/25.01  thf('107', plain,
% 24.73/25.01      ((((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F)
% 24.73/25.01          = (k1_funct_1 @ sk_E @ 
% 24.73/25.01             (sk_D_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F) @ 
% 24.73/25.01              sk_E)))
% 24.73/25.01        | ~ (v1_funct_1 @ sk_E)
% 24.73/25.01        | ~ (v1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['104', '106'])).
% 24.73/25.01  thf('108', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('109', plain, ((v1_relat_1 @ sk_E)),
% 24.73/25.01      inference('sup-', [status(thm)], ['80', '81'])).
% 24.73/25.01  thf('110', plain,
% 24.73/25.01      (((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F)
% 24.73/25.01         = (k1_funct_1 @ sk_E @ 
% 24.73/25.01            (sk_D_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F) @ sk_E)))),
% 24.73/25.01      inference('demod', [status(thm)], ['107', '108', '109'])).
% 24.73/25.01  thf('111', plain,
% 24.73/25.01      (![X0 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X0)
% 24.73/25.01          | ~ (v1_funct_1 @ X0)
% 24.73/25.01          | ((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ X0) @ sk_F)
% 24.73/25.01              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 24.73/25.01      inference('sup-', [status(thm)], ['87', '93'])).
% 24.73/25.01  thf('112', plain,
% 24.73/25.01      ((r2_hidden @ (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)) @ 
% 24.73/25.01        (k2_relat_1 @ sk_E))),
% 24.73/25.01      inference('demod', [status(thm)], ['97', '98', '99'])).
% 24.73/25.01  thf('113', plain,
% 24.73/25.01      (![X9 : $i, X12 : $i]:
% 24.73/25.01         (~ (v1_relat_1 @ X9)
% 24.73/25.01          | ~ (v1_funct_1 @ X9)
% 24.73/25.01          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 24.73/25.01          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 24.73/25.01      inference('simplify', [status(thm)], ['105'])).
% 24.73/25.01  thf('114', plain,
% 24.73/25.01      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01          = (k1_funct_1 @ sk_E @ 
% 24.73/25.01             (sk_D_1 @ (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)) @ 
% 24.73/25.01              sk_E)))
% 24.73/25.01        | ~ (v1_funct_1 @ sk_E)
% 24.73/25.01        | ~ (v1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup-', [status(thm)], ['112', '113'])).
% 24.73/25.01  thf('115', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('116', plain, ((v1_relat_1 @ sk_E)),
% 24.73/25.01      inference('sup-', [status(thm)], ['80', '81'])).
% 24.73/25.01  thf('117', plain,
% 24.73/25.01      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01         = (k1_funct_1 @ sk_E @ 
% 24.73/25.01            (sk_D_1 @ (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)) @ sk_E)))),
% 24.73/25.01      inference('demod', [status(thm)], ['114', '115', '116'])).
% 24.73/25.01  thf('118', plain,
% 24.73/25.01      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01          = (k1_funct_1 @ sk_E @ 
% 24.73/25.01             (sk_D_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F) @ 
% 24.73/25.01              sk_E)))
% 24.73/25.01        | ~ (v1_funct_1 @ sk_E)
% 24.73/25.01        | ~ (v1_relat_1 @ sk_E))),
% 24.73/25.01      inference('sup+', [status(thm)], ['111', '117'])).
% 24.73/25.01  thf('119', plain, ((v1_funct_1 @ sk_E)),
% 24.73/25.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.73/25.01  thf('120', plain, ((v1_relat_1 @ sk_E)),
% 24.73/25.01      inference('sup-', [status(thm)], ['80', '81'])).
% 24.73/25.01  thf('121', plain,
% 24.73/25.01      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01         = (k1_funct_1 @ sk_E @ 
% 24.73/25.01            (sk_D_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F) @ sk_E)))),
% 24.73/25.01      inference('demod', [status(thm)], ['118', '119', '120'])).
% 24.73/25.01  thf('122', plain,
% 24.73/25.01      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 24.73/25.01         = (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F))),
% 24.73/25.01      inference('sup+', [status(thm)], ['110', '121'])).
% 24.73/25.01  thf('123', plain,
% 24.73/25.01      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 24.73/25.01         sk_F) != (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F))),
% 24.73/25.01      inference('demod', [status(thm)], ['86', '122'])).
% 24.73/25.01  thf('124', plain,
% 24.73/25.01      ((((k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F)
% 24.73/25.01          != (k1_funct_1 @ (k5_relat_1 @ sk_D_2 @ sk_E) @ sk_F))
% 24.73/25.01        | ((sk_C_2) = (k1_xboole_0)))),
% 24.73/25.01      inference('sup-', [status(thm)], ['30', '123'])).
% 24.73/25.01  thf('125', plain, (((sk_C_2) = (k1_xboole_0))),
% 24.73/25.01      inference('simplify', [status(thm)], ['124'])).
% 24.73/25.01  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.73/25.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.73/25.01  thf('127', plain, ($false),
% 24.73/25.01      inference('demod', [status(thm)], ['0', '125', '126'])).
% 24.73/25.01  
% 24.73/25.01  % SZS output end Refutation
% 24.73/25.01  
% 24.73/25.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
