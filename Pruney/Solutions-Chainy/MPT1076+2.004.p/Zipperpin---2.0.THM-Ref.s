%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gh3LKFfqpU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 620 expanded)
%              Number of leaves         :   46 ( 196 expanded)
%              Depth                    :   22
%              Number of atoms          : 2262 (15350 expanded)
%              Number of equality atoms :   70 ( 312 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t193_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                 => ! [F: $i] :
                      ( ( m1_subset_1 @ F @ B )
                     => ( ( v1_partfun1 @ E @ A )
                       => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                          = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                   => ! [F: $i] :
                        ( ( m1_subset_1 @ F @ B )
                       => ( ( v1_partfun1 @ E @ A )
                         => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                            = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t193_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_A )
    | ( ( k1_relat_1 @ sk_E )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['7','12','15'])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['4','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('19',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X49 @ X47 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X47 @ X48 @ X51 @ X46 @ X50 ) @ X49 )
        = ( k1_funct_1 @ X50 @ ( k1_funct_1 @ X46 @ X49 ) ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X47 @ X48 @ X46 ) @ ( k1_relset_1 @ X48 @ X51 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','38','39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['43','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ sk_B )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['70','71','74'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','80'])).

thf('82',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['59','81'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('84',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t176_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X44 )
      | ( ( k7_partfun1 @ X42 @ X45 @ X43 )
        = ( k3_funct_2 @ X44 @ X42 @ X45 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('90',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X23 )
      | ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('98',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( v1_partfun1 @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('99',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['96','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('108',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['107','115'])).

thf('117',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['106','116'])).

thf('118',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['54','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C )
        & ( m1_subset_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('122',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X44 )
      | ( ( k7_partfun1 @ X42 @ X45 @ X43 )
        = ( k3_funct_2 @ X44 @ X42 @ X45 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['132','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36 ) @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['142','148'])).

thf('150',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','141','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','152'])).

thf('154',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['118','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('161',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['149','150'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['159','168'])).

thf('170',plain,
    ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('171',plain,
    ( ( k7_partfun1 @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['158','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['42','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['173','174'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('176',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['0','175','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gh3LKFfqpU
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 128 iterations in 0.066s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(t193_funct_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52           ( ![C:$i,D:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.52                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.52               ( ![E:$i]:
% 0.21/0.52                 ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                     ( m1_subset_1 @
% 0.21/0.52                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.52                   ( ![F:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.52                       ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.52                         ( ( k3_funct_2 @
% 0.21/0.52                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.52                           ( k7_partfun1 @
% 0.21/0.52                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52              ( ![C:$i,D:$i]:
% 0.21/0.52                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.52                    ( m1_subset_1 @
% 0.21/0.52                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.52                  ( ![E:$i]:
% 0.21/0.52                    ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                        ( m1_subset_1 @
% 0.21/0.52                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.52                      ( ![F:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.52                          ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.52                            ( ( k3_funct_2 @
% 0.21/0.52                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.52                              ( k7_partfun1 @
% 0.21/0.52                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.21/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.52  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d4_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i]:
% 0.21/0.52         (~ (v1_partfun1 @ X32 @ X31)
% 0.21/0.52          | ((k1_relat_1 @ X32) = (X31))
% 0.21/0.52          | ~ (v4_relat_1 @ X32 @ X31)
% 0.21/0.52          | ~ (v1_relat_1 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_E)
% 0.21/0.52        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.21/0.52        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.52          | (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf(fc6_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.52  thf('12', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         ((v4_relat_1 @ X13 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('15', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '12', '15'])).
% 0.21/0.52  thf('17', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t185_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.52           ( ![E:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.52               ( ![F:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.52                   ( ( r1_tarski @
% 0.21/0.52                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.52                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.52                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.52                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X46)
% 0.21/0.52          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.21/0.52          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.21/0.52          | ~ (m1_subset_1 @ X49 @ X47)
% 0.21/0.52          | ((k1_funct_1 @ (k8_funct_2 @ X47 @ X48 @ X51 @ X46 @ X50) @ X49)
% 0.21/0.52              = (k1_funct_1 @ X50 @ (k1_funct_1 @ X46 @ X49)))
% 0.21/0.52          | ((X47) = (k1_xboole_0))
% 0.21/0.52          | ~ (r1_tarski @ (k2_relset_1 @ X47 @ X48 @ X46) @ 
% 0.21/0.52               (k1_relset_1 @ X48 @ X51 @ X50))
% 0.21/0.52          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X51)))
% 0.21/0.52          | ~ (v1_funct_1 @ X50)
% 0.21/0.52          | (v1_xboole_0 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.52          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.21/0.52               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.21/0.52          | ((sk_B) = (k1_xboole_0))
% 0.21/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.52              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.52         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.52          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.21/0.52          | ((sk_B) = (k1_xboole_0))
% 0.21/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.52              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '23', '24', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.52          | ((sk_B) = (k1_xboole_0))
% 0.21/0.52          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         ((v5_relat_1 @ X13 @ X15)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf(d19_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (v5_relat_1 @ X6 @ X7)
% 0.21/0.52          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.21/0.52          | ~ (v1_relat_1 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.52          | (v1_relat_1 @ X4)
% 0.21/0.52          | ~ (v1_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.52  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.52          | ((sk_B) = (k1_xboole_0))
% 0.21/0.52          | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '38', '39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | ((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.21/0.52             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.52         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.52       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.21/0.52          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.21/0.52          | ~ (v1_funct_1 @ X38)
% 0.21/0.52          | (v1_xboole_0 @ X39)
% 0.21/0.52          | ~ (m1_subset_1 @ X41 @ X39)
% 0.21/0.52          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.52  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '53'])).
% 0.21/0.52  thf('55', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t2_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((r2_hidden @ X2 @ X3)
% 0.21/0.52          | (v1_xboole_0 @ X3)
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.52  thf('57', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('59', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.21/0.52      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc5_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.52             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.21/0.52          | (v1_partfun1 @ X28 @ X29)
% 0.21/0.52          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.21/0.52          | ~ (v1_funct_1 @ X28)
% 0.21/0.52          | (v1_xboole_0 @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.21/0.52        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('65', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.52  thf('67', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.21/0.52      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i]:
% 0.21/0.52         (~ (v1_partfun1 @ X32 @ X31)
% 0.21/0.52          | ((k1_relat_1 @ X32) = (X31))
% 0.21/0.52          | ~ (v4_relat_1 @ X32 @ X31)
% 0.21/0.52          | ~ (v1_relat_1 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.52        | ~ (v4_relat_1 @ sk_D @ sk_B)
% 0.21/0.52        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         ((v4_relat_1 @ X13 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('74', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.52  thf('75', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.21/0.52  thf(t172_funct_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.52           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ X12)
% 0.21/0.52          | ~ (v1_funct_1 @ X11)
% 0.21/0.52          | ~ (v5_relat_1 @ X11 @ X12)
% 0.21/0.52          | ~ (v1_relat_1 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.52          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.21/0.52          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ sk_A)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['60', '80'])).
% 0.21/0.52  thf('82', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['59', '81'])).
% 0.21/0.52  thf(t1_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.52  thf('84', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t176_funct_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.52                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.21/0.52                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X42)
% 0.21/0.52          | ~ (m1_subset_1 @ X43 @ X44)
% 0.21/0.52          | ((k7_partfun1 @ X42 @ X45 @ X43)
% 0.21/0.52              = (k3_funct_2 @ X44 @ X42 @ X45 @ X43))
% 0.21/0.52          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.21/0.52          | ~ (v1_funct_2 @ X45 @ X44 @ X42)
% 0.21/0.52          | ~ (v1_funct_1 @ X45)
% 0.21/0.52          | (v1_xboole_0 @ X44))),
% 0.21/0.52      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.52          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.52              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.21/0.52         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X22)
% 0.21/0.52          | ~ (v1_partfun1 @ X22 @ X23)
% 0.21/0.52          | (v1_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.52        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.52  thf('92', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('93', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('94', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.21/0.52  thf('95', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_A)
% 0.21/0.52          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.52              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['87', '88', '94'])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_C)
% 0.21/0.52        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.52            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['84', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.21/0.52  thf('98', plain,
% 0.21/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X25)
% 0.21/0.52          | ~ (v1_xboole_0 @ X26)
% 0.21/0.52          | ~ (v1_partfun1 @ X27 @ X25)
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.52        | ~ (v1_xboole_0 @ sk_C)
% 0.21/0.52        | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.52  thf('100', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('101', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.52  thf('102', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('103', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.52      inference('clc', [status(thm)], ['101', '102'])).
% 0.21/0.52  thf('104', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_A)
% 0.21/0.52        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.52            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.52      inference('clc', [status(thm)], ['96', '103'])).
% 0.21/0.52  thf('105', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('106', plain,
% 0.21/0.52      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.52         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('clc', [status(thm)], ['104', '105'])).
% 0.21/0.52  thf('107', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('109', plain,
% 0.21/0.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.21/0.52          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.21/0.52          | ~ (v1_funct_1 @ X38)
% 0.21/0.52          | (v1_xboole_0 @ X39)
% 0.21/0.52          | ~ (m1_subset_1 @ X41 @ X39)
% 0.21/0.52          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.52  thf('110', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_A)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.52  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('112', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.21/0.52  thf('113', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | (v1_xboole_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.21/0.52  thf('114', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('115', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.52          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['113', '114'])).
% 0.21/0.52  thf('116', plain,
% 0.21/0.52      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.52         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['107', '115'])).
% 0.21/0.52  thf('117', plain,
% 0.21/0.52      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.52         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['106', '116'])).
% 0.21/0.52  thf('118', plain,
% 0.21/0.52      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '117'])).
% 0.21/0.52  thf('119', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('120', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('121', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k8_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_funct_1 @ E ) & 
% 0.21/0.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.52       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.21/0.52         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.21/0.52         ( m1_subset_1 @
% 0.21/0.52           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.52           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.21/0.52  thf('122', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.21/0.52          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.21/0.52          | ~ (v1_funct_1 @ X33)
% 0.21/0.52          | ~ (v1_funct_1 @ X36)
% 0.21/0.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 0.21/0.52          | (m1_subset_1 @ (k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X37))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.21/0.52  thf('123', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.52  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('125', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('126', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.52          | ~ (v1_funct_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.21/0.52  thf('127', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.52        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['120', '126'])).
% 0.21/0.52  thf('128', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('129', plain,
% 0.21/0.52      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['127', '128'])).
% 0.21/0.52  thf('130', plain,
% 0.21/0.52      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X42)
% 0.21/0.52          | ~ (m1_subset_1 @ X43 @ X44)
% 0.21/0.52          | ((k7_partfun1 @ X42 @ X45 @ X43)
% 0.21/0.52              = (k3_funct_2 @ X44 @ X42 @ X45 @ X43))
% 0.21/0.52          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.21/0.52          | ~ (v1_funct_2 @ X45 @ X44 @ X42)
% 0.21/0.52          | ~ (v1_funct_1 @ X45)
% 0.21/0.52          | (v1_xboole_0 @ X44))),
% 0.21/0.52      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.21/0.52  thf('131', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.21/0.52          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52               sk_B @ sk_C)
% 0.21/0.52          | ((k7_partfun1 @ sk_C @ 
% 0.21/0.52              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52              = (k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['129', '130'])).
% 0.21/0.52  thf('132', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('133', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('134', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.21/0.52          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.21/0.52          | ~ (v1_funct_1 @ X33)
% 0.21/0.52          | ~ (v1_funct_1 @ X36)
% 0.21/0.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 0.21/0.52          | (v1_funct_1 @ (k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.21/0.52  thf('135', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['133', '134'])).
% 0.21/0.52  thf('136', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('137', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('138', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.21/0.52  thf('139', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.52        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['132', '138'])).
% 0.21/0.52  thf('140', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('141', plain,
% 0.21/0.52      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.21/0.52      inference('demod', [status(thm)], ['139', '140'])).
% 0.21/0.52  thf('142', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('143', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('144', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.21/0.52          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.21/0.52          | ~ (v1_funct_1 @ X33)
% 0.21/0.52          | ~ (v1_funct_1 @ X36)
% 0.21/0.52          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 0.21/0.52          | (v1_funct_2 @ (k8_funct_2 @ X34 @ X35 @ X37 @ X33 @ X36) @ X34 @ 
% 0.21/0.52             X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.21/0.52  thf('145', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.52          | ~ (v1_funct_1 @ X1)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['143', '144'])).
% 0.21/0.52  thf('146', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('147', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('148', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.52          | ~ (v1_funct_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.21/0.52  thf('149', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.52        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52           sk_B @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['142', '148'])).
% 0.21/0.52  thf('150', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('151', plain,
% 0.21/0.52      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.21/0.52        sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['149', '150'])).
% 0.21/0.52  thf('152', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ sk_B)
% 0.21/0.52          | ((k7_partfun1 @ sk_C @ 
% 0.21/0.52              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52              = (k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['131', '141', '151'])).
% 0.21/0.52  thf('153', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_C)
% 0.21/0.52        | ((k7_partfun1 @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52            = (k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52               (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))
% 0.21/0.52        | (v1_xboole_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['119', '152'])).
% 0.21/0.52  thf('154', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.52      inference('clc', [status(thm)], ['101', '102'])).
% 0.21/0.52  thf('155', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_B)
% 0.21/0.52        | ((k7_partfun1 @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52            = (k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52               (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)))),
% 0.21/0.52      inference('clc', [status(thm)], ['153', '154'])).
% 0.21/0.52  thf('156', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('157', plain,
% 0.21/0.52      (((k7_partfun1 @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         = (k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.21/0.52      inference('clc', [status(thm)], ['155', '156'])).
% 0.21/0.52  thf('158', plain,
% 0.21/0.52      (((k7_partfun1 @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['118', '157'])).
% 0.21/0.52  thf('159', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('160', plain,
% 0.21/0.52      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['127', '128'])).
% 0.21/0.52  thf('161', plain,
% 0.21/0.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.21/0.52          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.21/0.52          | ~ (v1_funct_1 @ X38)
% 0.21/0.52          | (v1_xboole_0 @ X39)
% 0.21/0.52          | ~ (m1_subset_1 @ X41 @ X39)
% 0.21/0.52          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.52  thf('162', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52               X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.21/0.52          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52               sk_B @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['160', '161'])).
% 0.21/0.52  thf('163', plain,
% 0.21/0.52      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.21/0.52      inference('demod', [status(thm)], ['139', '140'])).
% 0.21/0.52  thf('164', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52               X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_B)
% 0.21/0.52          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52               sk_B @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['162', '163'])).
% 0.21/0.52  thf('165', plain,
% 0.21/0.52      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.21/0.52        sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['149', '150'])).
% 0.21/0.52  thf('166', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52               X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | (v1_xboole_0 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['164', '165'])).
% 0.21/0.52  thf('167', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('168', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.52          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.52              = (k1_funct_1 @ 
% 0.21/0.52                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['166', '167'])).
% 0.21/0.52  thf('169', plain,
% 0.21/0.52      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['159', '168'])).
% 0.21/0.52  thf('170', plain,
% 0.21/0.52      (((k7_partfun1 @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         = (k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.52            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.21/0.52      inference('clc', [status(thm)], ['155', '156'])).
% 0.21/0.52  thf('171', plain,
% 0.21/0.52      (((k7_partfun1 @ sk_C @ 
% 0.21/0.52         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.21/0.52      inference('sup+', [status(thm)], ['169', '170'])).
% 0.21/0.52  thf('172', plain,
% 0.21/0.52      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.52         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['158', '171'])).
% 0.21/0.52  thf('173', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['42', '172'])).
% 0.21/0.52  thf('174', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('175', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['173', '174'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('176', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('177', plain, ($false),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '175', '176'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
