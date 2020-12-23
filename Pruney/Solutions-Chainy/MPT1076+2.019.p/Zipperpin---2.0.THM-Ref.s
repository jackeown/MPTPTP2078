%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gHj5vOrpLR

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 715 expanded)
%              Number of leaves         :   42 ( 225 expanded)
%              Depth                    :   18
%              Number of atoms          : 1947 (16415 expanded)
%              Number of equality atoms :   62 ( 361 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf(t186_funct_2,axiom,(
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

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X38 @ X39 @ X41 @ X37 @ X42 ) @ X40 )
        = ( k7_partfun1 @ X41 @ X42 @ ( k1_funct_1 @ X37 @ X40 ) ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X38 @ X39 @ X37 ) @ ( k1_relset_1 @ X39 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t186_funct_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k7_partfun1 @ X1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
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
        = ( k7_partfun1 @ X1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
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
        = ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','38','39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ X21 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X21 @ X22 @ X20 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k3_funct_2 @ X30 @ X31 @ X29 @ X32 )
        = ( k1_funct_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['52','62'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ X35 )
      | ( ( k7_partfun1 @ X33 @ X36 @ X34 )
        = ( k3_funct_2 @ X35 @ X33 @ X36 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['10','11'])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['72','73'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X44 )
      | ( v1_funct_2 @ X43 @ ( k1_relat_1 @ X43 ) @ X44 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ sk_E @ ( k1_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['10','11'])).

thf('78',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_E @ ( k1_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['7','12','15'])).

thf('81',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( v1_partfun1 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('86',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['83','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['52','62'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k3_funct_2 @ X30 @ X31 @ X29 @ X32 )
        = ( k1_funct_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['94','102'])).

thf('104',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['93','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['42','104'])).

thf('106',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('108',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['93','103'])).

thf('110',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X25 @ X26 @ X28 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k3_funct_2 @ X30 @ X31 @ X29 @ X32 )
        = ( k1_funct_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X25 @ X26 @ X28 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['124','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X25 @ X26 @ X28 @ X24 @ X27 ) @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['134','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','133','143'])).

thf('145',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['111','146'])).

thf('148',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['110','147'])).

thf('149',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['105','148'])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['149','150'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('152',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['0','151','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gHj5vOrpLR
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 155 iterations in 0.102s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.57  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(t193_funct_2, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.57           ( ![C:$i,D:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.57                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.57               ( ![E:$i]:
% 0.21/0.57                 ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.57                     ( m1_subset_1 @
% 0.21/0.57                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.57                   ( ![F:$i]:
% 0.21/0.57                     ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.57                       ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.57                         ( ( k3_funct_2 @
% 0.21/0.57                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.57                           ( k7_partfun1 @
% 0.21/0.57                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.57              ( ![C:$i,D:$i]:
% 0.21/0.57                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.57                    ( m1_subset_1 @
% 0.21/0.57                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.57                  ( ![E:$i]:
% 0.21/0.57                    ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.57                        ( m1_subset_1 @
% 0.21/0.57                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.57                      ( ![F:$i]:
% 0.21/0.57                        ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.57                          ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.57                            ( ( k3_funct_2 @
% 0.21/0.57                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.57                              ( k7_partfun1 @
% 0.21/0.57                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.21/0.57  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.57         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.57  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d4_partfun1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.57       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (v1_partfun1 @ X19 @ X18)
% 0.21/0.57          | ((k1_relat_1 @ X19) = (X18))
% 0.21/0.57          | ~ (v4_relat_1 @ X19 @ X18)
% 0.21/0.57          | ~ (v1_relat_1 @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_E)
% 0.21/0.57        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.21/0.57        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.57          | (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf(fc6_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('12', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         ((v4_relat_1 @ X6 @ X7)
% 0.21/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('15', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.57  thf('16', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['7', '12', '15'])).
% 0.21/0.57  thf('17', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t186_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.57           ( ![E:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.57                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.57               ( ![F:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.57                   ( ( r1_tarski @
% 0.21/0.57                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.57                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.57                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.57                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X37)
% 0.21/0.57          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.21/0.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.21/0.57          | ~ (m1_subset_1 @ X40 @ X38)
% 0.21/0.57          | ((k1_funct_1 @ (k8_funct_2 @ X38 @ X39 @ X41 @ X37 @ X42) @ X40)
% 0.21/0.57              = (k7_partfun1 @ X41 @ X42 @ (k1_funct_1 @ X37 @ X40)))
% 0.21/0.57          | ((X38) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ (k2_relset_1 @ X38 @ X39 @ X37) @ 
% 0.21/0.57               (k1_relset_1 @ X39 @ X41 @ X42))
% 0.21/0.57          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X41)))
% 0.21/0.57          | ~ (v1_funct_1 @ X42)
% 0.21/0.57          | (v1_xboole_0 @ X39))),
% 0.21/0.57      inference('cnf', [status(esa)], [t186_funct_2])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.57          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.21/0.57               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.57              = (k7_partfun1 @ X1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.57          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.21/0.57              = (k7_partfun1 @ X1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '23', '24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.57              = (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.21/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.57          | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         ((v5_relat_1 @ X6 @ X8)
% 0.21/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf(d19_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ B ) =>
% 0.21/0.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (v5_relat_1 @ X2 @ X3)
% 0.21/0.57          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.57          | ~ (v1_relat_1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.57          | (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.57              = (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['27', '38', '39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_A)
% 0.21/0.57        | ((sk_B) = (k1_xboole_0))
% 0.21/0.57        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57            = (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '41'])).
% 0.21/0.57  thf('43', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k3_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.57         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.57       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.57          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.21/0.57          | ~ (v1_funct_1 @ X20)
% 0.21/0.57          | (v1_xboole_0 @ X21)
% 0.21/0.57          | ~ (m1_subset_1 @ X23 @ X21)
% 0.21/0.57          | (m1_subset_1 @ (k3_funct_2 @ X21 @ X22 @ X20 @ X23) @ X22))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (v1_xboole_0 @ sk_B)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (v1_xboole_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.57  thf('50', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A))),
% 0.21/0.57      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['43', '51'])).
% 0.21/0.57  thf('53', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.57         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.57       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.57          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.21/0.57          | ~ (v1_funct_1 @ X29)
% 0.21/0.57          | (v1_xboole_0 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ X30)
% 0.21/0.57          | ((k3_funct_2 @ X30 @ X31 @ X29 @ X32) = (k1_funct_1 @ X29 @ X32)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (v1_xboole_0 @ sk_B)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (v1_xboole_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.57  thf('60', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.57      inference('sup-', [status(thm)], ['53', '61'])).
% 0.21/0.57  thf('63', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['52', '62'])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t176_funct_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.57                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.21/0.57                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ X33)
% 0.21/0.57          | ~ (m1_subset_1 @ X34 @ X35)
% 0.21/0.57          | ((k7_partfun1 @ X33 @ X36 @ X34)
% 0.21/0.57              = (k3_funct_2 @ X35 @ X33 @ X36 @ X34))
% 0.21/0.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 0.21/0.57          | ~ (v1_funct_2 @ X36 @ X35 @ X33)
% 0.21/0.57          | ~ (v1_funct_1 @ X36)
% 0.21/0.57          | (v1_xboole_0 @ X35))),
% 0.21/0.57      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.57          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.57              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.57          | (v1_xboole_0 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.57  thf('67', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         ((v5_relat_1 @ X6 @ X8)
% 0.21/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.57  thf('70', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 0.21/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (v5_relat_1 @ X2 @ X3)
% 0.21/0.57          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.57          | ~ (v1_relat_1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.57  thf('73', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('74', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.57  thf(t4_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.57       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.57         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.21/0.57           ( m1_subset_1 @
% 0.21/0.57             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X43 : $i, X44 : $i]:
% 0.21/0.57         (~ (r1_tarski @ (k2_relat_1 @ X43) @ X44)
% 0.21/0.57          | (v1_funct_2 @ X43 @ (k1_relat_1 @ X43) @ X44)
% 0.21/0.57          | ~ (v1_funct_1 @ X43)
% 0.21/0.57          | ~ (v1_relat_1 @ X43))),
% 0.21/0.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_E)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.57        | (v1_funct_2 @ sk_E @ (k1_relat_1 @ sk_E) @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.57  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('78', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('79', plain, ((v1_funct_2 @ sk_E @ (k1_relat_1 @ sk_E) @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.21/0.57  thf('80', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['7', '12', '15'])).
% 0.21/0.57  thf('81', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_A)
% 0.21/0.57          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.57              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.57          | (v1_xboole_0 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['66', '67', '81'])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.57            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.57        | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['63', '82'])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc2_partfun1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ X15)
% 0.21/0.57          | ~ (v1_xboole_0 @ X16)
% 0.21/0.57          | ~ (v1_partfun1 @ X17 @ X15)
% 0.21/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.57        | ~ (v1_xboole_0 @ sk_C)
% 0.21/0.57        | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.57  thf('87', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('88', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('89', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('90', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.57      inference('clc', [status(thm)], ['88', '89'])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_A)
% 0.21/0.57        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.57            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.57      inference('clc', [status(thm)], ['83', '90'])).
% 0.21/0.57  thf('92', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.57         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.57  thf('94', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['52', '62'])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.57          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.21/0.57          | ~ (v1_funct_1 @ X29)
% 0.21/0.57          | (v1_xboole_0 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ X30)
% 0.21/0.57          | ((k3_funct_2 @ X30 @ X31 @ X29 @ X32) = (k1_funct_1 @ X29 @ X32)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.57  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('99', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('100', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.57          | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.21/0.57  thf('101', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.57          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.57         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['94', '102'])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.57         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['93', '103'])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_A)
% 0.21/0.57        | ((sk_B) = (k1_xboole_0))
% 0.21/0.57        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.57      inference('demod', [status(thm)], ['42', '104'])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.21/0.57             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.57      inference('sup-', [status(thm)], ['53', '61'])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.57  thf('109', plain,
% 0.21/0.57      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.57         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['93', '103'])).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.57  thf('111', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('112', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k8_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.57         ( v1_funct_1 @ E ) & 
% 0.21/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.57       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.21/0.57         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.21/0.57         ( m1_subset_1 @
% 0.21/0.57           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.21/0.57  thf('114', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.57          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.57          | ~ (v1_funct_1 @ X24)
% 0.21/0.57          | ~ (v1_funct_1 @ X27)
% 0.21/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 0.21/0.57          | (m1_subset_1 @ (k8_funct_2 @ X25 @ X26 @ X28 @ X24 @ X27) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X28))))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.57          | ~ (v1_funct_1 @ X1)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['113', '114'])).
% 0.21/0.57  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('117', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('118', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.57          | ~ (v1_funct_1 @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.57        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '118'])).
% 0.21/0.57  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.57          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.21/0.57          | ~ (v1_funct_1 @ X29)
% 0.21/0.57          | (v1_xboole_0 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ X30)
% 0.21/0.57          | ((k3_funct_2 @ X30 @ X31 @ X29 @ X32) = (k1_funct_1 @ X29 @ X32)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.57  thf('123', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.57            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.57               X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (v1_xboole_0 @ sk_B)
% 0.21/0.57          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.21/0.57          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.57               sk_B @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('125', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('126', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.57          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.57          | ~ (v1_funct_1 @ X24)
% 0.21/0.57          | ~ (v1_funct_1 @ X27)
% 0.21/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 0.21/0.57          | (v1_funct_1 @ (k8_funct_2 @ X25 @ X26 @ X28 @ X24 @ X27)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.21/0.57  thf('127', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.57  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('129', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.21/0.57          | ~ (v1_funct_1 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.57        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['124', '130'])).
% 0.21/0.57  thf('132', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.21/0.57      inference('demod', [status(thm)], ['131', '132'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('135', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('136', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.57          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.57          | ~ (v1_funct_1 @ X24)
% 0.21/0.57          | ~ (v1_funct_1 @ X27)
% 0.21/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 0.21/0.57          | (v1_funct_2 @ (k8_funct_2 @ X25 @ X26 @ X28 @ X24 @ X27) @ X25 @ 
% 0.21/0.57             X28))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.21/0.57  thf('137', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.57          | ~ (v1_funct_1 @ X1)
% 0.21/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['135', '136'])).
% 0.21/0.57  thf('138', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('139', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('140', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.57          | ~ (v1_funct_1 @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['137', '138', '139'])).
% 0.21/0.57  thf('141', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.57        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.57           sk_B @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['134', '140'])).
% 0.21/0.57  thf('142', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('143', plain,
% 0.21/0.57      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.21/0.57        sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['141', '142'])).
% 0.21/0.57  thf('144', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.57            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.57               X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | (v1_xboole_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['123', '133', '143'])).
% 0.21/0.57  thf('145', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('146', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.57          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.57              = (k1_funct_1 @ 
% 0.21/0.57                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['144', '145'])).
% 0.21/0.57  thf('147', plain,
% 0.21/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.21/0.57      inference('sup-', [status(thm)], ['111', '146'])).
% 0.21/0.57  thf('148', plain,
% 0.21/0.57      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.57         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.57      inference('demod', [status(thm)], ['110', '147'])).
% 0.21/0.57  thf('149', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['105', '148'])).
% 0.21/0.57  thf('150', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('151', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.57      inference('clc', [status(thm)], ['149', '150'])).
% 0.21/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.57  thf('152', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('153', plain, ($false),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '151', '152'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
