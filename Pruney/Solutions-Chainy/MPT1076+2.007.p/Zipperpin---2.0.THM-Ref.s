%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HDJ7rX0b30

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:29 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 377 expanded)
%              Number of leaves         :   42 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          : 1897 (9526 expanded)
%              Number of equality atoms :   59 ( 216 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ X41 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X41 @ X42 @ X45 @ X40 @ X44 ) @ X43 )
        = ( k1_funct_1 @ X44 @ ( k1_funct_1 @ X40 @ X43 ) ) )
      | ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X41 @ X42 @ X40 ) @ ( k1_relset_1 @ X42 @ X45 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ( v1_xboole_0 @ X42 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k3_funct_2 @ X33 @ X34 @ X32 @ X35 )
        = ( k1_funct_1 @ X32 @ X35 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X31 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X28 @ X29 @ X31 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X31 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k3_funct_2 @ X33 @ X34 @ X32 @ X35 )
        = ( k1_funct_1 @ X32 @ X35 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X31 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X28 @ X29 @ X31 @ X27 @ X30 ) ) ) ),
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
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X31 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X28 @ X29 @ X31 @ X27 @ X30 ) @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['55','91'])).

thf('93',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['54','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('96',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ X24 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X24 @ X25 @ X23 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('105',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
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

thf('107',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X38 )
      | ( ( k7_partfun1 @ X36 @ X39 @ X37 )
        = ( k3_funct_2 @ X38 @ X36 @ X39 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('111',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_partfun1 @ X15 @ X16 )
      | ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('112',plain,
    ( ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','115'])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('119',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( v1_partfun1 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('120',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['117','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['103','104'])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k3_funct_2 @ X33 @ X34 @ X32 @ X35 )
        = ( k1_funct_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['127','137'])).

thf('139',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['93','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['42','139'])).

thf('141',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['140','141'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('143',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['0','142','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HDJ7rX0b30
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 104 iterations in 0.079s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.55  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.36/0.55  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.55  thf(t193_funct_2, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.55           ( ![C:$i,D:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.36/0.55                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.36/0.55               ( ![E:$i]:
% 0.36/0.55                 ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                     ( m1_subset_1 @
% 0.36/0.55                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.36/0.55                   ( ![F:$i]:
% 0.36/0.55                     ( ( m1_subset_1 @ F @ B ) =>
% 0.36/0.55                       ( ( v1_partfun1 @ E @ A ) =>
% 0.36/0.55                         ( ( k3_funct_2 @
% 0.36/0.55                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.36/0.55                           ( k7_partfun1 @
% 0.36/0.55                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.55              ( ![C:$i,D:$i]:
% 0.36/0.55                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.36/0.55                    ( m1_subset_1 @
% 0.36/0.55                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.36/0.55                  ( ![E:$i]:
% 0.36/0.55                    ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                        ( m1_subset_1 @
% 0.36/0.55                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.36/0.55                      ( ![F:$i]:
% 0.36/0.55                        ( ( m1_subset_1 @ F @ B ) =>
% 0.36/0.55                          ( ( v1_partfun1 @ E @ A ) =>
% 0.36/0.55                            ( ( k3_funct_2 @
% 0.36/0.55                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.36/0.55                              ( k7_partfun1 @
% 0.36/0.55                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.36/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.55         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.36/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.55  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d4_partfun1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.55       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (v1_partfun1 @ X22 @ X21)
% 0.36/0.55          | ((k1_relat_1 @ X22) = (X21))
% 0.36/0.55          | ~ (v4_relat_1 @ X22 @ X21)
% 0.36/0.55          | ~ (v1_relat_1 @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ sk_E)
% 0.36/0.55        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.36/0.55        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc2_relat_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.55          | (v1_relat_1 @ X0)
% 0.36/0.55          | ~ (v1_relat_1 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf(fc6_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.55  thf('12', plain, ((v1_relat_1 @ sk_E)),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         ((v4_relat_1 @ X6 @ X7)
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.55  thf('15', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['7', '12', '15'])).
% 0.36/0.55  thf('17', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t185_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.36/0.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.36/0.55           ( ![E:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.55                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.36/0.55               ( ![F:$i]:
% 0.36/0.55                 ( ( m1_subset_1 @ F @ B ) =>
% 0.36/0.55                   ( ( r1_tarski @
% 0.36/0.55                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.36/0.55                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.36/0.55                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.55                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.36/0.55                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.36/0.55         (~ (v1_funct_1 @ X40)
% 0.36/0.55          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.36/0.55          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.36/0.55          | ~ (m1_subset_1 @ X43 @ X41)
% 0.36/0.55          | ((k1_funct_1 @ (k8_funct_2 @ X41 @ X42 @ X45 @ X40 @ X44) @ X43)
% 0.36/0.55              = (k1_funct_1 @ X44 @ (k1_funct_1 @ X40 @ X43)))
% 0.36/0.55          | ((X41) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ (k2_relset_1 @ X41 @ X42 @ X40) @ 
% 0.36/0.55               (k1_relset_1 @ X42 @ X45 @ X44))
% 0.36/0.55          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X45)))
% 0.36/0.55          | ~ (v1_funct_1 @ X44)
% 0.36/0.55          | (v1_xboole_0 @ X42))),
% 0.36/0.55      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ sk_A)
% 0.36/0.55          | ~ (v1_funct_1 @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.36/0.55          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.36/0.55               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.36/0.55          | ((sk_B) = (k1_xboole_0))
% 0.36/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.36/0.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.36/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ sk_A)
% 0.36/0.55          | ~ (v1_funct_1 @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.36/0.55          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.36/0.55          | ((sk_B) = (k1_xboole_0))
% 0.36/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.36/0.55              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '23', '24', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.36/0.55              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.36/0.55          | ((sk_B) = (k1_xboole_0))
% 0.36/0.55          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.55          | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         ((v5_relat_1 @ X6 @ X8)
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.55  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf(d19_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ B ) =>
% 0.36/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (v5_relat_1 @ X2 @ X3)
% 0.36/0.55          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.36/0.55          | ~ (v1_relat_1 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.55          | (v1_relat_1 @ X0)
% 0.36/0.55          | ~ (v1_relat_1 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.55  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['32', '37'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.36/0.55              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.36/0.55          | ((sk_B) = (k1_xboole_0))
% 0.36/0.55          | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['27', '38', '39', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_A)
% 0.36/0.55        | ((sk_B) = (k1_xboole_0))
% 0.36/0.55        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.36/0.55            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.36/0.55         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.36/0.55             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('44', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k3_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.36/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.36/0.55       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.36/0.55          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.36/0.55          | ~ (v1_funct_1 @ X32)
% 0.36/0.55          | (v1_xboole_0 @ X33)
% 0.36/0.55          | ~ (m1_subset_1 @ X35 @ X33)
% 0.36/0.55          | ((k3_funct_2 @ X33 @ X34 @ X32 @ X35) = (k1_funct_1 @ X32 @ X35)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.36/0.55  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.36/0.55      inference('clc', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '52'])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.36/0.55         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.36/0.55      inference('demod', [status(thm)], ['43', '53'])).
% 0.36/0.55  thf('55', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k8_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( v1_funct_1 @ E ) & 
% 0.36/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.36/0.55       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.36/0.55         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.36/0.55         ( m1_subset_1 @
% 0.36/0.55           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.36/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.36/0.55          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.36/0.55          | ~ (v1_funct_1 @ X27)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X31)))
% 0.36/0.55          | (m1_subset_1 @ (k8_funct_2 @ X28 @ X29 @ X31 @ X27 @ X30) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X31))))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.55          | ~ (v1_funct_1 @ X1)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.55  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.55          | ~ (v1_funct_1 @ X1))),
% 0.36/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.36/0.55  thf('63', plain,
% 0.36/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.36/0.55        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['56', '62'])).
% 0.36/0.55  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.36/0.55          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.36/0.55          | ~ (v1_funct_1 @ X32)
% 0.36/0.55          | (v1_xboole_0 @ X33)
% 0.36/0.55          | ~ (m1_subset_1 @ X35 @ X33)
% 0.36/0.55          | ((k3_funct_2 @ X33 @ X34 @ X32 @ X35) = (k1_funct_1 @ X32 @ X35)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.36/0.55            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55               X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B)
% 0.36/0.55          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.36/0.55          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55               sk_B @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.55  thf('68', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('70', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.36/0.55          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.36/0.55          | ~ (v1_funct_1 @ X27)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X31)))
% 0.36/0.55          | (v1_funct_1 @ (k8_funct_2 @ X28 @ X29 @ X31 @ X27 @ X30)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.36/0.55  thf('71', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.36/0.55          | ~ (v1_funct_1 @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.55  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('74', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.36/0.55          | ~ (v1_funct_1 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.36/0.55        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['68', '74'])).
% 0.36/0.55  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.36/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.55  thf('78', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.36/0.55            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55               X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B)
% 0.36/0.55          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55               sk_B @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['67', '77'])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('81', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.36/0.55          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.36/0.55          | ~ (v1_funct_1 @ X27)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X31)))
% 0.36/0.55          | (v1_funct_2 @ (k8_funct_2 @ X28 @ X29 @ X31 @ X27 @ X30) @ X28 @ 
% 0.36/0.55             X31))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.36/0.55  thf('82', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.55          | ~ (v1_funct_1 @ X1)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['80', '81'])).
% 0.36/0.55  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('84', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('85', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.36/0.55          | ~ (v1_funct_1 @ X1))),
% 0.36/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      ((~ (v1_funct_1 @ sk_E)
% 0.36/0.55        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55           sk_B @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['79', '85'])).
% 0.36/0.55  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('88', plain,
% 0.36/0.55      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.36/0.55        sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.36/0.55  thf('89', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.36/0.55            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.36/0.55               X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['78', '88'])).
% 0.36/0.55  thf('90', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('91', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.36/0.55              = (k1_funct_1 @ 
% 0.36/0.55                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.36/0.55      inference('clc', [status(thm)], ['89', '90'])).
% 0.36/0.55  thf('92', plain,
% 0.36/0.55      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.36/0.55         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.36/0.55         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.36/0.55      inference('sup-', [status(thm)], ['55', '91'])).
% 0.36/0.55  thf('93', plain,
% 0.36/0.55      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.36/0.55         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.36/0.55      inference('demod', [status(thm)], ['54', '92'])).
% 0.36/0.55  thf('94', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('95', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k3_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.36/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.36/0.55  thf('96', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.36/0.55          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.36/0.55          | ~ (v1_funct_1 @ X23)
% 0.36/0.55          | (v1_xboole_0 @ X24)
% 0.36/0.55          | ~ (m1_subset_1 @ X26 @ X24)
% 0.36/0.55          | (m1_subset_1 @ (k3_funct_2 @ X24 @ X25 @ X23 @ X26) @ X25))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.36/0.55  thf('97', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.36/0.55  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('99', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('100', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (v1_xboole_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.36/0.55  thf('101', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('102', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.36/0.55          | (m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['100', '101'])).
% 0.36/0.55  thf('103', plain,
% 0.36/0.55      ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['94', '102'])).
% 0.36/0.55  thf('104', plain,
% 0.36/0.55      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '52'])).
% 0.36/0.55  thf('105', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['103', '104'])).
% 0.36/0.55  thf('106', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t176_funct_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.55                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( m1_subset_1 @ D @ A ) =>
% 0.36/0.55                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.36/0.55                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('107', plain,
% 0.36/0.55      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X36)
% 0.36/0.55          | ~ (m1_subset_1 @ X37 @ X38)
% 0.36/0.55          | ((k7_partfun1 @ X36 @ X39 @ X37)
% 0.36/0.55              = (k3_funct_2 @ X38 @ X36 @ X39 @ X37))
% 0.36/0.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 0.36/0.55          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 0.36/0.55          | ~ (v1_funct_1 @ X39)
% 0.36/0.55          | (v1_xboole_0 @ X38))),
% 0.36/0.55      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.36/0.55  thf('108', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ sk_A)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.36/0.55          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.36/0.55              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.36/0.55          | (v1_xboole_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.36/0.55  thf('109', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('110', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.36/0.55         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.36/0.55  thf('111', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (v1_funct_1 @ X15)
% 0.36/0.55          | ~ (v1_partfun1 @ X15 @ X16)
% 0.36/0.55          | (v1_funct_2 @ X15 @ X16 @ X17)
% 0.36/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.36/0.55  thf('112', plain,
% 0.36/0.55      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.36/0.55        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.36/0.55        | ~ (v1_funct_1 @ sk_E))),
% 0.36/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.36/0.55  thf('113', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('114', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('115', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.36/0.55  thf('116', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ sk_A)
% 0.36/0.55          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.36/0.55              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.36/0.55          | (v1_xboole_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['108', '109', '115'])).
% 0.36/0.55  thf('117', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_C)
% 0.36/0.55        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.36/0.55            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.36/0.55        | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['105', '116'])).
% 0.36/0.55  thf('118', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc2_partfun1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.36/0.55       ( ![C:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.36/0.55  thf('119', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X18)
% 0.36/0.55          | ~ (v1_xboole_0 @ X19)
% 0.36/0.55          | ~ (v1_partfun1 @ X20 @ X18)
% 0.36/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.36/0.55  thf('120', plain,
% 0.36/0.55      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.36/0.55        | ~ (v1_xboole_0 @ sk_C)
% 0.36/0.55        | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['118', '119'])).
% 0.36/0.55  thf('121', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('122', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['120', '121'])).
% 0.36/0.55  thf('123', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('124', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.36/0.55      inference('clc', [status(thm)], ['122', '123'])).
% 0.36/0.55  thf('125', plain,
% 0.36/0.55      (((v1_xboole_0 @ sk_A)
% 0.36/0.55        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.36/0.55            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.36/0.55      inference('clc', [status(thm)], ['117', '124'])).
% 0.36/0.55  thf('126', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('127', plain,
% 0.36/0.55      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.36/0.55         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.36/0.55      inference('clc', [status(thm)], ['125', '126'])).
% 0.36/0.55  thf('128', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['103', '104'])).
% 0.36/0.55  thf('129', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('130', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.36/0.55          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.36/0.55          | ~ (v1_funct_1 @ X32)
% 0.36/0.55          | (v1_xboole_0 @ X33)
% 0.36/0.55          | ~ (m1_subset_1 @ X35 @ X33)
% 0.36/0.55          | ((k3_funct_2 @ X33 @ X34 @ X32 @ X35) = (k1_funct_1 @ X32 @ X35)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.36/0.55  thf('131', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.36/0.55          | (v1_xboole_0 @ sk_A)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['129', '130'])).
% 0.36/0.55  thf('132', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('133', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.36/0.55  thf('134', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.36/0.55          | (v1_xboole_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.36/0.55  thf('135', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('136', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.36/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.36/0.55      inference('clc', [status(thm)], ['134', '135'])).
% 0.36/0.55  thf('137', plain,
% 0.36/0.55      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.36/0.55         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['128', '136'])).
% 0.36/0.55  thf('138', plain,
% 0.36/0.55      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.36/0.55         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['127', '137'])).
% 0.36/0.55  thf('139', plain,
% 0.36/0.55      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.36/0.55         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.36/0.55      inference('demod', [status(thm)], ['93', '138'])).
% 0.36/0.55  thf('140', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['42', '139'])).
% 0.36/0.55  thf('141', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('142', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.55      inference('clc', [status(thm)], ['140', '141'])).
% 0.36/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.55  thf('143', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('144', plain, ($false),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '142', '143'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
