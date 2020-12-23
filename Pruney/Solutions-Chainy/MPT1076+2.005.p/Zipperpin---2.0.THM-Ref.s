%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01zYb7TU1K

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 431 expanded)
%              Number of leaves         :   45 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          : 1959 (9895 expanded)
%              Number of equality atoms :   60 ( 215 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ X37 )
      | ( ( k3_funct_2 @ X37 @ X38 @ X36 @ X39 )
        = ( k1_funct_1 @ X36 @ X39 ) ) ) ),
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

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X35 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X32 @ X33 @ X35 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ X37 )
      | ( ( k3_funct_2 @ X37 @ X38 @ X36 @ X39 )
        = ( k1_funct_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X35 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X32 @ X33 @ X35 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X35 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X32 @ X33 @ X35 @ X31 @ X34 ) @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','77','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['55','90'])).

thf('92',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['54','91'])).

thf('93',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('94',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ sk_B )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('110',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('112',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['108','109','112'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('114',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X9 @ X8 ) @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['35','36'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['93','119'])).

thf('121',plain,(
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

thf('122',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ X42 )
      | ( ( k7_partfun1 @ X40 @ X43 @ X41 )
        = ( k3_funct_2 @ X42 @ X40 @ X43 @ X41 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('126',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X21 )
      | ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('127',plain,
    ( ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','124','130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('134',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( v1_partfun1 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('135',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['132','139'])).

thf('141',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['93','119'])).

thf('144',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ X37 )
      | ( ( k3_funct_2 @ X37 @ X38 @ X36 @ X39 )
        = ( k1_funct_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['143','151'])).

thf('153',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['142','152'])).

thf('154',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['92','153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['42','154'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['155','156'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('158',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['0','157','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.01zYb7TU1K
% 0.13/0.37  % Computer   : n003.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 15:22:42 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 113 iterations in 0.063s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.23/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.55  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.23/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.23/0.55  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.23/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.23/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.23/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.55  thf(t193_funct_2, conjecture,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.55           ( ![C:$i,D:$i]:
% 0.23/0.55             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.23/0.55                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.23/0.55               ( ![E:$i]:
% 0.23/0.55                 ( ( ( v1_funct_1 @ E ) & 
% 0.23/0.55                     ( m1_subset_1 @
% 0.23/0.55                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.23/0.55                   ( ![F:$i]:
% 0.23/0.55                     ( ( m1_subset_1 @ F @ B ) =>
% 0.23/0.55                       ( ( v1_partfun1 @ E @ A ) =>
% 0.23/0.55                         ( ( k3_funct_2 @
% 0.23/0.55                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.23/0.55                           ( k7_partfun1 @
% 0.23/0.55                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i]:
% 0.23/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55          ( ![B:$i]:
% 0.23/0.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.55              ( ![C:$i,D:$i]:
% 0.23/0.55                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.23/0.55                    ( m1_subset_1 @
% 0.23/0.55                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.23/0.55                  ( ![E:$i]:
% 0.23/0.55                    ( ( ( v1_funct_1 @ E ) & 
% 0.23/0.55                        ( m1_subset_1 @
% 0.23/0.55                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.23/0.55                      ( ![F:$i]:
% 0.23/0.55                        ( ( m1_subset_1 @ F @ B ) =>
% 0.23/0.55                          ( ( v1_partfun1 @ E @ A ) =>
% 0.23/0.55                            ( ( k3_funct_2 @
% 0.23/0.55                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.23/0.55                              ( k7_partfun1 @
% 0.23/0.55                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.23/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.55  thf('3', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.55         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.23/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.55  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.23/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.55  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(d4_partfun1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.23/0.55       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X29 : $i, X30 : $i]:
% 0.23/0.55         (~ (v1_partfun1 @ X30 @ X29)
% 0.23/0.55          | ((k1_relat_1 @ X30) = (X29))
% 0.23/0.55          | ~ (v4_relat_1 @ X30 @ X29)
% 0.23/0.55          | ~ (v1_relat_1 @ X30))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      ((~ (v1_relat_1 @ sk_E)
% 0.23/0.55        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.23/0.55        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(cc2_relat_1, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ A ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X2 : $i, X3 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.23/0.55          | (v1_relat_1 @ X2)
% 0.23/0.55          | ~ (v1_relat_1 @ X3))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.23/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.55  thf(fc6_relat_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.23/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.55  thf('12', plain, ((v1_relat_1 @ sk_E)),
% 0.23/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.55  thf('13', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(cc2_relset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.55         ((v4_relat_1 @ X11 @ X12)
% 0.23/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.55  thf('15', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.55  thf('16', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['7', '12', '15'])).
% 0.23/0.55  thf('17', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['4', '16'])).
% 0.23/0.55  thf('18', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t185_funct_2, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.23/0.55       ( ![D:$i]:
% 0.23/0.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.23/0.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.23/0.55           ( ![E:$i]:
% 0.23/0.55             ( ( ( v1_funct_1 @ E ) & 
% 0.23/0.55                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.23/0.55               ( ![F:$i]:
% 0.23/0.55                 ( ( m1_subset_1 @ F @ B ) =>
% 0.23/0.55                   ( ( r1_tarski @
% 0.23/0.55                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.23/0.55                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.23/0.55                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.55                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.23/0.55                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.23/0.55         (~ (v1_funct_1 @ X44)
% 0.23/0.55          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.23/0.55          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.23/0.55          | ~ (m1_subset_1 @ X47 @ X45)
% 0.23/0.55          | ((k1_funct_1 @ (k8_funct_2 @ X45 @ X46 @ X49 @ X44 @ X48) @ X47)
% 0.23/0.55              = (k1_funct_1 @ X48 @ (k1_funct_1 @ X44 @ X47)))
% 0.23/0.55          | ((X45) = (k1_xboole_0))
% 0.23/0.55          | ~ (r1_tarski @ (k2_relset_1 @ X45 @ X46 @ X44) @ 
% 0.23/0.55               (k1_relset_1 @ X46 @ X49 @ X48))
% 0.23/0.55          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X49)))
% 0.23/0.55          | ~ (v1_funct_1 @ X48)
% 0.23/0.55          | (v1_xboole_0 @ X46))),
% 0.23/0.55      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ sk_A)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.23/0.55          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.23/0.55               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.23/0.55          | ((sk_B) = (k1_xboole_0))
% 0.23/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.23/0.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.23/0.55          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.23/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.55  thf('21', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.23/0.55  thf('22', plain,
% 0.23/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.55         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.23/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.23/0.55  thf('23', plain,
% 0.23/0.55      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.23/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.55  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ sk_A)
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.23/0.55          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.23/0.55          | ((sk_B) = (k1_xboole_0))
% 0.23/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.23/0.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.23/0.55          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['20', '23', '24', '25'])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.23/0.55              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.23/0.55          | ((sk_B) = (k1_xboole_0))
% 0.23/0.55          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.23/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.23/0.55          | (v1_xboole_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['17', '26'])).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('29', plain,
% 0.23/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.55         ((v5_relat_1 @ X11 @ X13)
% 0.23/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.55  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.55  thf(d19_relat_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( v1_relat_1 @ B ) =>
% 0.23/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      (![X4 : $i, X5 : $i]:
% 0.23/0.55         (~ (v5_relat_1 @ X4 @ X5)
% 0.23/0.55          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.23/0.55          | ~ (v1_relat_1 @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('34', plain,
% 0.23/0.55      (![X2 : $i, X3 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.23/0.55          | (v1_relat_1 @ X2)
% 0.23/0.55          | ~ (v1_relat_1 @ X3))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.55  thf('35', plain,
% 0.23/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.23/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.55  thf('36', plain,
% 0.23/0.55      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.23/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.55  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.55  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.23/0.55      inference('demod', [status(thm)], ['32', '37'])).
% 0.23/0.55  thf('39', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('41', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.23/0.55              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.23/0.55          | ((sk_B) = (k1_xboole_0))
% 0.23/0.55          | (v1_xboole_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['27', '38', '39', '40'])).
% 0.23/0.55  thf('42', plain,
% 0.23/0.55      (((v1_xboole_0 @ sk_A)
% 0.23/0.55        | ((sk_B) = (k1_xboole_0))
% 0.23/0.55        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.23/0.55            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['1', '41'])).
% 0.23/0.55  thf('43', plain,
% 0.23/0.55      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.23/0.55         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.23/0.55         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.23/0.55             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('44', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('45', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(redefinition_k3_funct_2, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.23/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.23/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.23/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.23/0.55       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.23/0.55  thf('46', plain,
% 0.23/0.55      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.23/0.55          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.23/0.55          | ~ (v1_funct_1 @ X36)
% 0.23/0.55          | (v1_xboole_0 @ X37)
% 0.23/0.55          | ~ (m1_subset_1 @ X39 @ X37)
% 0.23/0.55          | ((k3_funct_2 @ X37 @ X38 @ X36 @ X39) = (k1_funct_1 @ X36 @ X39)))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.23/0.55  thf('47', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | (v1_xboole_0 @ sk_B)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.23/0.55  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('50', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | (v1_xboole_0 @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.23/0.55  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('52', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.23/0.55      inference('clc', [status(thm)], ['50', '51'])).
% 0.23/0.55  thf('53', plain,
% 0.23/0.55      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.23/0.55      inference('sup-', [status(thm)], ['44', '52'])).
% 0.23/0.55  thf('54', plain,
% 0.23/0.55      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.23/0.55         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.23/0.55         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.23/0.55      inference('demod', [status(thm)], ['43', '53'])).
% 0.23/0.55  thf('55', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('56', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('57', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(dt_k8_funct_2, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.23/0.55         ( v1_funct_1 @ E ) & 
% 0.23/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.23/0.55       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.23/0.55         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.23/0.55         ( m1_subset_1 @
% 0.23/0.55           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.23/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.23/0.55  thf('58', plain,
% 0.23/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.23/0.55          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.23/0.55          | ~ (v1_funct_1 @ X31)
% 0.23/0.55          | ~ (v1_funct_1 @ X34)
% 0.23/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X35)))
% 0.23/0.55          | (m1_subset_1 @ (k8_funct_2 @ X32 @ X33 @ X35 @ X31 @ X34) @ 
% 0.23/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X35))))),
% 0.23/0.55      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.23/0.55  thf('59', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.23/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.23/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.23/0.55          | ~ (v1_funct_1 @ X1)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.23/0.55  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('62', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.23/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.23/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.23/0.55          | ~ (v1_funct_1 @ X1))),
% 0.23/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.23/0.55  thf('63', plain,
% 0.23/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.23/0.55        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.23/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['56', '62'])).
% 0.23/0.55  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('65', plain,
% 0.23/0.55      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.23/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.23/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.23/0.55  thf('66', plain,
% 0.23/0.55      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.23/0.55          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.23/0.55          | ~ (v1_funct_1 @ X36)
% 0.23/0.55          | (v1_xboole_0 @ X37)
% 0.23/0.55          | ~ (m1_subset_1 @ X39 @ X37)
% 0.23/0.55          | ((k3_funct_2 @ X37 @ X38 @ X36 @ X39) = (k1_funct_1 @ X36 @ X39)))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.23/0.55  thf('67', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.23/0.55            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.23/0.55            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.23/0.55               X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | (v1_xboole_0 @ sk_B)
% 0.23/0.55          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.23/0.55          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.23/0.55               sk_B @ sk_C))),
% 0.23/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.55  thf('68', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('69', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('70', plain,
% 0.23/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.23/0.55          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.23/0.55          | ~ (v1_funct_1 @ X31)
% 0.23/0.55          | ~ (v1_funct_1 @ X34)
% 0.23/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X35)))
% 0.23/0.55          | (v1_funct_1 @ (k8_funct_2 @ X32 @ X33 @ X35 @ X31 @ X34)))),
% 0.23/0.55      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.23/0.55  thf('71', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.23/0.55          | ~ (v1_funct_1 @ X0)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.23/0.55  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('74', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.23/0.55          | ~ (v1_funct_1 @ X0))),
% 0.23/0.55      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.23/0.55  thf('75', plain,
% 0.23/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.23/0.55        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['68', '74'])).
% 0.23/0.55  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('77', plain,
% 0.23/0.55      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.23/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.23/0.55  thf('78', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('79', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('80', plain,
% 0.23/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.23/0.55          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.23/0.55          | ~ (v1_funct_1 @ X31)
% 0.23/0.55          | ~ (v1_funct_1 @ X34)
% 0.23/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X35)))
% 0.23/0.55          | (v1_funct_2 @ (k8_funct_2 @ X32 @ X33 @ X35 @ X31 @ X34) @ X32 @ 
% 0.23/0.55             X35))),
% 0.23/0.55      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.23/0.55  thf('81', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.23/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.23/0.55          | ~ (v1_funct_1 @ X1)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.23/0.55  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('83', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('84', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.23/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.23/0.55          | ~ (v1_funct_1 @ X1))),
% 0.23/0.55      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.23/0.55  thf('85', plain,
% 0.23/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.23/0.55        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.23/0.55           sk_B @ sk_C))),
% 0.23/0.55      inference('sup-', [status(thm)], ['78', '84'])).
% 0.23/0.55  thf('86', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('87', plain,
% 0.23/0.55      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.23/0.55        sk_C)),
% 0.23/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.23/0.55  thf('88', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.23/0.55            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.23/0.55            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.23/0.55               X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | (v1_xboole_0 @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['67', '77', '87'])).
% 0.23/0.55  thf('89', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('90', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.23/0.55          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.23/0.55              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.23/0.55              = (k1_funct_1 @ 
% 0.23/0.55                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.23/0.55      inference('clc', [status(thm)], ['88', '89'])).
% 0.23/0.55  thf('91', plain,
% 0.23/0.55      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.23/0.55         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.23/0.55         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.23/0.55      inference('sup-', [status(thm)], ['55', '90'])).
% 0.23/0.55  thf('92', plain,
% 0.23/0.55      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.23/0.55         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.23/0.55      inference('demod', [status(thm)], ['54', '91'])).
% 0.23/0.55  thf('93', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.55  thf('94', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t2_subset, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.55  thf('95', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((r2_hidden @ X0 @ X1)
% 0.23/0.55          | (v1_xboole_0 @ X1)
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.55  thf('96', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.23/0.55  thf('97', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('98', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.23/0.55      inference('clc', [status(thm)], ['96', '97'])).
% 0.23/0.55  thf('99', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(cc5_funct_2, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.55       ( ![C:$i]:
% 0.23/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.55           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.23/0.55             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.23/0.55  thf('100', plain,
% 0.23/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.23/0.55          | (v1_partfun1 @ X26 @ X27)
% 0.23/0.55          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.23/0.55          | ~ (v1_funct_1 @ X26)
% 0.23/0.55          | (v1_xboole_0 @ X28))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.23/0.55  thf('101', plain,
% 0.23/0.55      (((v1_xboole_0 @ sk_A)
% 0.23/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.23/0.55        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.23/0.55        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['99', '100'])).
% 0.23/0.55  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('103', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('104', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.23/0.55  thf('105', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('106', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.23/0.55      inference('clc', [status(thm)], ['104', '105'])).
% 0.23/0.55  thf('107', plain,
% 0.23/0.55      (![X29 : $i, X30 : $i]:
% 0.23/0.55         (~ (v1_partfun1 @ X30 @ X29)
% 0.23/0.55          | ((k1_relat_1 @ X30) = (X29))
% 0.23/0.55          | ~ (v4_relat_1 @ X30 @ X29)
% 0.23/0.55          | ~ (v1_relat_1 @ X30))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.23/0.55  thf('108', plain,
% 0.23/0.55      ((~ (v1_relat_1 @ sk_D)
% 0.23/0.55        | ~ (v4_relat_1 @ sk_D @ sk_B)
% 0.23/0.55        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.23/0.55  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.55  thf('110', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('111', plain,
% 0.23/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.55         ((v4_relat_1 @ X11 @ X12)
% 0.23/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.55  thf('112', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.23/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.23/0.55  thf('113', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['108', '109', '112'])).
% 0.23/0.55  thf(t176_funct_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.55       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.23/0.55         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.23/0.55  thf('114', plain,
% 0.23/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X8 @ (k1_relat_1 @ X9))
% 0.23/0.55          | (m1_subset_1 @ (k1_funct_1 @ X9 @ X8) @ X10)
% 0.23/0.55          | ~ (v1_funct_1 @ X9)
% 0.23/0.55          | ~ (v5_relat_1 @ X9 @ X10)
% 0.23/0.55          | ~ (v1_relat_1 @ X9))),
% 0.23/0.55      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.23/0.55  thf('115', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X0 @ sk_B)
% 0.23/0.55          | ~ (v1_relat_1 @ sk_D)
% 0.23/0.55          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.55          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.23/0.55  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.55  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('118', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X0 @ sk_B)
% 0.23/0.55          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.23/0.55          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.23/0.55      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.23/0.55  thf('119', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ X0)
% 0.23/0.55          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['98', '118'])).
% 0.23/0.55  thf('120', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['93', '119'])).
% 0.23/0.55  thf('121', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t176_funct_2, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.55           ( ![C:$i]:
% 0.23/0.55             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.23/0.55                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.55               ( ![D:$i]:
% 0.23/0.55                 ( ( m1_subset_1 @ D @ A ) =>
% 0.23/0.55                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.23/0.55                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.23/0.55  thf('122', plain,
% 0.23/0.55      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X40)
% 0.23/0.55          | ~ (m1_subset_1 @ X41 @ X42)
% 0.23/0.55          | ((k7_partfun1 @ X40 @ X43 @ X41)
% 0.23/0.55              = (k3_funct_2 @ X42 @ X40 @ X43 @ X41))
% 0.23/0.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 0.23/0.55          | ~ (v1_funct_2 @ X43 @ X42 @ X40)
% 0.23/0.55          | ~ (v1_funct_1 @ X43)
% 0.23/0.55          | (v1_xboole_0 @ X42))),
% 0.23/0.55      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.23/0.55  thf('123', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ sk_A)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.23/0.55          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.23/0.55              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.55          | (v1_xboole_0 @ sk_C))),
% 0.23/0.55      inference('sup-', [status(thm)], ['121', '122'])).
% 0.23/0.55  thf('124', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('125', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(cc1_funct_2, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.55       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.23/0.55         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.23/0.55  thf('126', plain,
% 0.23/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.55         (~ (v1_funct_1 @ X20)
% 0.23/0.55          | ~ (v1_partfun1 @ X20 @ X21)
% 0.23/0.55          | (v1_funct_2 @ X20 @ X21 @ X22)
% 0.23/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.23/0.55  thf('127', plain,
% 0.23/0.55      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.23/0.55        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.23/0.55        | ~ (v1_funct_1 @ sk_E))),
% 0.23/0.55      inference('sup-', [status(thm)], ['125', '126'])).
% 0.23/0.55  thf('128', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('130', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.23/0.55      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.23/0.55  thf('131', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ sk_A)
% 0.23/0.55          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.23/0.55              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.55          | (v1_xboole_0 @ sk_C))),
% 0.23/0.55      inference('demod', [status(thm)], ['123', '124', '130'])).
% 0.23/0.55  thf('132', plain,
% 0.23/0.55      (((v1_xboole_0 @ sk_C)
% 0.23/0.55        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.23/0.55            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.23/0.55        | (v1_xboole_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['120', '131'])).
% 0.23/0.55  thf('133', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(cc2_partfun1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.23/0.55       ( ![C:$i]:
% 0.23/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.55           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.23/0.55  thf('134', plain,
% 0.23/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X23)
% 0.23/0.55          | ~ (v1_xboole_0 @ X24)
% 0.23/0.55          | ~ (v1_partfun1 @ X25 @ X23)
% 0.23/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.23/0.55      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.23/0.55  thf('135', plain,
% 0.23/0.55      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.23/0.55        | ~ (v1_xboole_0 @ sk_C)
% 0.23/0.55        | (v1_xboole_0 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['133', '134'])).
% 0.23/0.55  thf('136', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('137', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['135', '136'])).
% 0.23/0.55  thf('138', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('139', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.23/0.55      inference('clc', [status(thm)], ['137', '138'])).
% 0.23/0.55  thf('140', plain,
% 0.23/0.55      (((v1_xboole_0 @ sk_A)
% 0.23/0.55        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.23/0.55            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.23/0.55      inference('clc', [status(thm)], ['132', '139'])).
% 0.23/0.55  thf('141', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('142', plain,
% 0.23/0.55      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.23/0.55         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.23/0.55      inference('clc', [status(thm)], ['140', '141'])).
% 0.23/0.55  thf('143', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['93', '119'])).
% 0.23/0.55  thf('144', plain,
% 0.23/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('145', plain,
% 0.23/0.55      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.23/0.55          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.23/0.55          | ~ (v1_funct_1 @ X36)
% 0.23/0.55          | (v1_xboole_0 @ X37)
% 0.23/0.55          | ~ (m1_subset_1 @ X39 @ X37)
% 0.23/0.55          | ((k3_funct_2 @ X37 @ X38 @ X36 @ X39) = (k1_funct_1 @ X36 @ X39)))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.23/0.55  thf('146', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.55          | (v1_xboole_0 @ sk_A)
% 0.23/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.23/0.55          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.23/0.55      inference('sup-', [status(thm)], ['144', '145'])).
% 0.23/0.55  thf('147', plain, ((v1_funct_1 @ sk_E)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('148', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.23/0.55      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.23/0.55  thf('149', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.23/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.55          | (v1_xboole_0 @ sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.23/0.55  thf('150', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('151', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.23/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.23/0.55      inference('clc', [status(thm)], ['149', '150'])).
% 0.23/0.55  thf('152', plain,
% 0.23/0.55      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.23/0.55         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['143', '151'])).
% 0.23/0.55  thf('153', plain,
% 0.23/0.55      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.23/0.55         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['142', '152'])).
% 0.23/0.55  thf('154', plain,
% 0.23/0.55      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.23/0.55         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.23/0.55      inference('demod', [status(thm)], ['92', '153'])).
% 0.23/0.55  thf('155', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['42', '154'])).
% 0.23/0.55  thf('156', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('157', plain, (((sk_B) = (k1_xboole_0))),
% 0.23/0.55      inference('clc', [status(thm)], ['155', '156'])).
% 0.23/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.55  thf('158', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.55  thf('159', plain, ($false),
% 0.23/0.55      inference('demod', [status(thm)], ['0', '157', '158'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
