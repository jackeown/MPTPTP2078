%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TzqTapnViP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:58 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 710 expanded)
%              Number of leaves         :   40 ( 224 expanded)
%              Depth                    :   30
%              Number of atoms          : 3475 (29037 expanded)
%              Number of equality atoms :  120 ( 979 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(t6_tmap_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ( ( r1_subset_1 @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ D @ B )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                           => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                                = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                              & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C )
                                = E )
                              & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D )
                                = F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                   => ( ( r1_subset_1 @ C @ D )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ C @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ D @ B )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                             => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                                  = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                                & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C )
                                  = E )
                                & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D )
                                  = F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tmap_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
        & ~ ( v1_xboole_0 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ C @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ D @ B )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k4_subset_1 @ A @ C @ D ) @ B )
        & ( m1_subset_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44 ) @ ( k4_subset_1 @ X43 @ X40 @ X42 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X43 @ X40 @ X42 ) @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(d1_tmap_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ D @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                         => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                              = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( k4_subset_1 @ A @ C @ D ) @ B )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) )
                               => ( ( G
                                    = ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                <=> ( ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ G @ C )
                                      = E )
                                    & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ G @ D )
                                      = F ) ) ) ) ) ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ( X38
       != ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 @ X38 @ X37 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X37 @ X32 @ X36 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) )
       != ( k2_partfun1 @ X33 @ X32 @ X35 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X32 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X32 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X32 ) ) )
      | ( ( k2_partfun1 @ X37 @ X32 @ X36 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) )
       != ( k2_partfun1 @ X33 @ X32 @ X35 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) @ X37 )
        = X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X5 @ X3 @ X4 )
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('66',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X12: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k9_relat_1 @ X13 @ X14 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('73',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('74',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('76',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_xboole_0 @ B @ C )
       => ( ( k5_relset_1 @ C @ A @ D @ B )
          = k1_xboole_0 ) ) ) )).

thf('80',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( ( k5_relset_1 @ X25 @ X27 @ X26 @ X24 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_relset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k5_relset_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k5_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('95',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( ( k5_relset_1 @ X25 @ X27 @ X26 @ X24 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_relset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relset_1 @ sk_D @ sk_B @ sk_F @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k5_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','86','87','88','93','102','103','104','105','106'])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('115',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('116',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('118',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('119',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('120',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('123',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','85'])).

thf('124',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','101'])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('128',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('130',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ( X38
       != ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 @ X38 @ X33 )
        = X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X37 @ X32 @ X36 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) )
       != ( k2_partfun1 @ X33 @ X32 @ X35 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X32 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('131',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X32 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X32 ) ) )
      | ( ( k2_partfun1 @ X37 @ X32 @ X36 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) )
       != ( k2_partfun1 @ X33 @ X32 @ X35 @ ( k9_subset_1 @ X34 @ X37 @ X33 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X34 @ X37 @ X33 ) @ X32 @ ( k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35 ) @ X33 )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('140',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','85'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('142',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('144',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','101'])).

thf('145',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139','140','141','142','143','144','145','146','147','148'])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['128','150'])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['127','152'])).

thf('154',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['111'])).

thf('156',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['111'])).

thf('167',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['126','165','166'])).

thf('168',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['112','167'])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['110','168'])).

thf('170',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','169'])).

thf('171',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    $false ),
    inference(demod,[status(thm)],['0','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TzqTapnViP
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.63  % Solved by: fo/fo7.sh
% 0.41/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.63  % done 200 iterations in 0.165s
% 0.41/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.63  % SZS output start Refutation
% 0.41/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.41/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.63  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.63  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.63  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.41/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.63  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.41/0.63  thf(t6_tmap_1, conjecture,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.63           ( ![C:$i]:
% 0.41/0.63             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.63                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.63               ( ![D:$i]:
% 0.41/0.63                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.63                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.63                   ( ( r1_subset_1 @ C @ D ) =>
% 0.41/0.63                     ( ![E:$i]:
% 0.41/0.63                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.41/0.63                           ( m1_subset_1 @
% 0.41/0.63                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.41/0.63                         ( ![F:$i]:
% 0.41/0.63                           ( ( ( v1_funct_1 @ F ) & 
% 0.41/0.63                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.41/0.63                               ( m1_subset_1 @
% 0.41/0.63                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.41/0.63                             ( ( ( k2_partfun1 @
% 0.41/0.63                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.41/0.63                                 ( k2_partfun1 @
% 0.41/0.63                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.41/0.63                               ( ( k2_partfun1 @
% 0.41/0.63                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.41/0.63                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.41/0.63                                 ( E ) ) & 
% 0.41/0.63                               ( ( k2_partfun1 @
% 0.41/0.63                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.41/0.63                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.41/0.63                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.63    (~( ![A:$i]:
% 0.41/0.63        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.63          ( ![B:$i]:
% 0.41/0.63            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.63              ( ![C:$i]:
% 0.41/0.63                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.63                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.63                  ( ![D:$i]:
% 0.41/0.63                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.63                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.63                      ( ( r1_subset_1 @ C @ D ) =>
% 0.41/0.63                        ( ![E:$i]:
% 0.41/0.63                          ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.63                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.41/0.63                              ( m1_subset_1 @
% 0.41/0.63                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.41/0.63                            ( ![F:$i]:
% 0.41/0.63                              ( ( ( v1_funct_1 @ F ) & 
% 0.41/0.63                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.41/0.63                                  ( m1_subset_1 @
% 0.41/0.63                                    F @ 
% 0.41/0.63                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.41/0.63                                ( ( ( k2_partfun1 @
% 0.41/0.63                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.41/0.63                                    ( k2_partfun1 @
% 0.41/0.63                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.41/0.63                                  ( ( k2_partfun1 @
% 0.41/0.63                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.41/0.63                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.41/0.63                                    ( E ) ) & 
% 0.41/0.63                                  ( ( k2_partfun1 @
% 0.41/0.63                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.41/0.63                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.41/0.63                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.63    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.41/0.63  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('2', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('3', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(dt_k1_tmap_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.63     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.63         ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.41/0.63         ( v1_funct_2 @ E @ C @ B ) & 
% 0.41/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.41/0.63         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.41/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.41/0.63       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.41/0.63         ( v1_funct_2 @
% 0.41/0.63           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.41/0.63           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.41/0.63         ( m1_subset_1 @
% 0.41/0.63           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.41/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.41/0.63  thf('4', plain,
% 0.41/0.63      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.41/0.63          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.41/0.63          | ~ (v1_funct_1 @ X39)
% 0.41/0.63          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.41/0.63          | (v1_xboole_0 @ X42)
% 0.41/0.63          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.41/0.63          | (v1_xboole_0 @ X40)
% 0.41/0.63          | (v1_xboole_0 @ X41)
% 0.41/0.63          | (v1_xboole_0 @ X43)
% 0.41/0.63          | ~ (v1_funct_1 @ X44)
% 0.41/0.63          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.41/0.63          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.41/0.63          | (v1_funct_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.41/0.63  thf('5', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.41/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | (v1_xboole_0 @ X2)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.41/0.63          | (v1_xboole_0 @ X1)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.41/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.63          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.63  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('8', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.41/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | (v1_xboole_0 @ X2)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.41/0.63          | (v1_xboole_0 @ X1)
% 0.41/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.41/0.63      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.41/0.63  thf('9', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_D)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (v1_funct_1 @ sk_F)
% 0.41/0.63          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.41/0.63          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['2', '8'])).
% 0.41/0.63  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('12', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_D)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.63      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.41/0.63  thf('13', plain,
% 0.41/0.63      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.63        | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('sup-', [status(thm)], ['1', '12'])).
% 0.41/0.63  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('15', plain,
% 0.41/0.63      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.63  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('17', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('18', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('19', plain,
% 0.41/0.63      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.41/0.63          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.41/0.63          | ~ (v1_funct_1 @ X39)
% 0.41/0.63          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.41/0.63          | (v1_xboole_0 @ X42)
% 0.41/0.63          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.41/0.63          | (v1_xboole_0 @ X40)
% 0.41/0.63          | (v1_xboole_0 @ X41)
% 0.41/0.63          | (v1_xboole_0 @ X43)
% 0.41/0.63          | ~ (v1_funct_1 @ X44)
% 0.41/0.63          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.41/0.63          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.41/0.63          | (v1_funct_2 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.41/0.63             (k4_subset_1 @ X43 @ X40 @ X42) @ X41))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.41/0.63  thf('20', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.41/0.63           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.41/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.41/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | (v1_xboole_0 @ X1)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.63          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.63  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('23', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.41/0.63           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.41/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.41/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | (v1_xboole_0 @ X1)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.41/0.63      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.63  thf('24', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_D)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (v1_funct_1 @ sk_F)
% 0.41/0.63          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.41/0.63          | (v1_funct_2 @ 
% 0.41/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['17', '23'])).
% 0.41/0.63  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('27', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_D)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | (v1_funct_2 @ 
% 0.41/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.41/0.63      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.63        | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('sup-', [status(thm)], ['16', '27'])).
% 0.41/0.63  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('30', plain,
% 0.41/0.63      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.63  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('32', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('33', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('34', plain,
% 0.41/0.63      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.41/0.63          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.41/0.63          | ~ (v1_funct_1 @ X39)
% 0.41/0.63          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.41/0.63          | (v1_xboole_0 @ X42)
% 0.41/0.63          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.41/0.63          | (v1_xboole_0 @ X40)
% 0.41/0.63          | (v1_xboole_0 @ X41)
% 0.41/0.63          | (v1_xboole_0 @ X43)
% 0.41/0.63          | ~ (v1_funct_1 @ X44)
% 0.41/0.63          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.41/0.63          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.41/0.63          | (m1_subset_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.41/0.63             (k1_zfmisc_1 @ 
% 0.41/0.63              (k2_zfmisc_1 @ (k4_subset_1 @ X43 @ X40 @ X42) @ X41))))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.41/0.63  thf('35', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.41/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.41/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.41/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | (v1_xboole_0 @ X1)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.63          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.63  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('38', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.41/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.41/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.41/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | (v1_xboole_0 @ X1)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.41/0.63      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.41/0.63  thf('39', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_D)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | ~ (v1_funct_1 @ sk_F)
% 0.41/0.63          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.41/0.63          | (m1_subset_1 @ 
% 0.41/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63             (k1_zfmisc_1 @ 
% 0.41/0.63              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['32', '38'])).
% 0.41/0.63  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('42', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_D)
% 0.41/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.41/0.63          | (v1_xboole_0 @ sk_C)
% 0.41/0.63          | (v1_xboole_0 @ sk_B)
% 0.41/0.63          | (v1_xboole_0 @ X0)
% 0.41/0.63          | (m1_subset_1 @ 
% 0.41/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63             (k1_zfmisc_1 @ 
% 0.41/0.63              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.41/0.63  thf('43', plain,
% 0.41/0.63      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63         (k1_zfmisc_1 @ 
% 0.41/0.63          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.63        | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('sup-', [status(thm)], ['31', '42'])).
% 0.41/0.63  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('45', plain,
% 0.41/0.63      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63         (k1_zfmisc_1 @ 
% 0.41/0.63          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | (v1_xboole_0 @ sk_D))),
% 0.41/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.63  thf(d1_tmap_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.63           ( ![C:$i]:
% 0.41/0.63             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.63                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.63               ( ![D:$i]:
% 0.41/0.63                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.63                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.63                   ( ![E:$i]:
% 0.41/0.63                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.41/0.63                         ( m1_subset_1 @
% 0.41/0.63                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.41/0.63                       ( ![F:$i]:
% 0.41/0.63                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.41/0.63                             ( m1_subset_1 @
% 0.41/0.63                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.41/0.63                           ( ( ( k2_partfun1 @
% 0.41/0.63                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.41/0.63                               ( k2_partfun1 @
% 0.41/0.63                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.41/0.63                             ( ![G:$i]:
% 0.41/0.63                               ( ( ( v1_funct_1 @ G ) & 
% 0.41/0.63                                   ( v1_funct_2 @
% 0.41/0.63                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.41/0.63                                   ( m1_subset_1 @
% 0.41/0.63                                     G @ 
% 0.41/0.63                                     ( k1_zfmisc_1 @
% 0.41/0.63                                       ( k2_zfmisc_1 @
% 0.41/0.63                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.41/0.63                                 ( ( ( G ) =
% 0.41/0.63                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.41/0.63                                   ( ( ( k2_partfun1 @
% 0.41/0.63                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.41/0.63                                         C ) =
% 0.41/0.63                                       ( E ) ) & 
% 0.41/0.63                                     ( ( k2_partfun1 @
% 0.41/0.63                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.41/0.63                                         D ) =
% 0.41/0.63                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.63  thf('46', plain,
% 0.41/0.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.63         ((v1_xboole_0 @ X32)
% 0.41/0.63          | (v1_xboole_0 @ X33)
% 0.41/0.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.41/0.63          | ~ (v1_funct_1 @ X35)
% 0.41/0.63          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.41/0.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.41/0.63          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.41/0.63          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X37)
% 0.41/0.63              = (X36))
% 0.41/0.63          | ~ (m1_subset_1 @ X38 @ 
% 0.41/0.63               (k1_zfmisc_1 @ 
% 0.41/0.63                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.41/0.63          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.41/0.63          | ~ (v1_funct_1 @ X38)
% 0.41/0.63          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.41/0.63              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.41/0.63                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.41/0.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.41/0.63          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.41/0.63          | ~ (v1_funct_1 @ X36)
% 0.41/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.41/0.63          | (v1_xboole_0 @ X37)
% 0.41/0.63          | (v1_xboole_0 @ X34))),
% 0.41/0.63      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.41/0.63  thf('47', plain,
% 0.41/0.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.63         ((v1_xboole_0 @ X34)
% 0.41/0.63          | (v1_xboole_0 @ X37)
% 0.41/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.41/0.63          | ~ (v1_funct_1 @ X36)
% 0.41/0.63          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.41/0.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.41/0.63          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.41/0.63              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.41/0.63                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.41/0.63          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.41/0.63          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.41/0.63               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.41/0.63          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.41/0.63               (k1_zfmisc_1 @ 
% 0.41/0.63                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.41/0.63          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.41/0.63              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X37) = (
% 0.41/0.63              X36))
% 0.41/0.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.41/0.63          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.41/0.63          | ~ (v1_funct_1 @ X35)
% 0.41/0.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.41/0.63          | (v1_xboole_0 @ X33)
% 0.41/0.63          | (v1_xboole_0 @ X32))),
% 0.41/0.63      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.63  thf('48', plain,
% 0.41/0.63      (((v1_xboole_0 @ sk_D)
% 0.41/0.63        | (v1_xboole_0 @ sk_C)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_A)
% 0.41/0.63        | (v1_xboole_0 @ sk_B)
% 0.41/0.63        | (v1_xboole_0 @ sk_D)
% 0.41/0.63        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.63        | ~ (v1_funct_1 @ sk_F)
% 0.41/0.63        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.41/0.63        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.41/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.63            = (sk_E))
% 0.41/0.63        | ~ (v1_funct_2 @ 
% 0.41/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.41/0.64        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.41/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.41/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.41/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_A))),
% 0.41/0.64      inference('sup-', [status(thm)], ['45', '47'])).
% 0.41/0.64  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('52', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf(redefinition_k9_subset_1, axiom,
% 0.41/0.64    (![A:$i,B:$i,C:$i]:
% 0.41/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.64       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.41/0.64  thf('54', plain,
% 0.41/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.64         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 0.41/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.41/0.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.41/0.64  thf('55', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.64  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf(redefinition_r1_subset_1, axiom,
% 0.41/0.64    (![A:$i,B:$i]:
% 0.41/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.41/0.64       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.41/0.64  thf('57', plain,
% 0.41/0.64      (![X15 : $i, X16 : $i]:
% 0.41/0.64         ((v1_xboole_0 @ X15)
% 0.41/0.64          | (v1_xboole_0 @ X16)
% 0.41/0.64          | (r1_xboole_0 @ X15 @ X16)
% 0.41/0.64          | ~ (r1_subset_1 @ X15 @ X16))),
% 0.41/0.64      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.41/0.64  thf('58', plain,
% 0.41/0.64      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C))),
% 0.41/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.64  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.41/0.64      inference('clc', [status(thm)], ['58', '59'])).
% 0.41/0.64  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.41/0.64      inference('clc', [status(thm)], ['60', '61'])).
% 0.41/0.64  thf(d7_xboole_0, axiom,
% 0.41/0.64    (![A:$i,B:$i]:
% 0.41/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.41/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.64  thf('63', plain,
% 0.41/0.64      (![X0 : $i, X1 : $i]:
% 0.41/0.64         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.41/0.64  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.64  thf('65', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf(redefinition_k2_partfun1, axiom,
% 0.41/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.64       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.41/0.64  thf('66', plain,
% 0.41/0.64      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.64         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.41/0.64          | ~ (v1_funct_1 @ X28)
% 0.41/0.64          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.41/0.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.41/0.64  thf('67', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.41/0.64          | ~ (v1_funct_1 @ sk_E))),
% 0.41/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.64  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('69', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.64  thf(t150_relat_1, axiom,
% 0.41/0.64    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.64  thf('70', plain,
% 0.41/0.64      (![X12 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.41/0.64      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.41/0.64  thf(t151_relat_1, axiom,
% 0.41/0.64    (![A:$i,B:$i]:
% 0.41/0.64     ( ( v1_relat_1 @ B ) =>
% 0.41/0.64       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.64         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.64  thf('71', plain,
% 0.41/0.64      (![X13 : $i, X14 : $i]:
% 0.41/0.64         (((k9_relat_1 @ X13 @ X14) != (k1_xboole_0))
% 0.41/0.64          | (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.41/0.64          | ~ (v1_relat_1 @ X13))),
% 0.41/0.64      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.41/0.64  thf('72', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.64          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.64  thf(t4_subset_1, axiom,
% 0.41/0.64    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.64  thf('73', plain,
% 0.41/0.64      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.41/0.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.64  thf(cc1_relset_1, axiom,
% 0.41/0.64    (![A:$i,B:$i,C:$i]:
% 0.41/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.64       ( v1_relat_1 @ C ) ))).
% 0.41/0.64  thf('74', plain,
% 0.41/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.64         ((v1_relat_1 @ X17)
% 0.41/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.41/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.64  thf('75', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.41/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.64  thf(t60_relat_1, axiom,
% 0.41/0.64    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.41/0.64     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.64  thf('76', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.41/0.64  thf('77', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['72', '75', '76'])).
% 0.41/0.64  thf('78', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.41/0.64      inference('simplify', [status(thm)], ['77'])).
% 0.41/0.64  thf('79', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf(t55_relset_1, axiom,
% 0.41/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.64     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.41/0.64       ( ( r1_xboole_0 @ B @ C ) =>
% 0.41/0.64         ( ( k5_relset_1 @ C @ A @ D @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.64  thf('80', plain,
% 0.41/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.64         (~ (r1_xboole_0 @ X24 @ X25)
% 0.41/0.64          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.41/0.64          | ((k5_relset_1 @ X25 @ X27 @ X26 @ X24) = (k1_xboole_0)))),
% 0.41/0.64      inference('cnf', [status(esa)], [t55_relset_1])).
% 0.41/0.64  thf('81', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k5_relset_1 @ sk_C @ sk_B @ sk_E @ X0) = (k1_xboole_0))
% 0.41/0.64          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.41/0.64      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.64  thf('82', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf(redefinition_k5_relset_1, axiom,
% 0.41/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.64       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.41/0.64  thf('83', plain,
% 0.41/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.64          | ((k5_relset_1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.41/0.64      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.41/0.64  thf('84', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k5_relset_1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.64  thf('85', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0))
% 0.41/0.64          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.41/0.64      inference('demod', [status(thm)], ['81', '84'])).
% 0.41/0.64  thf('86', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['78', '85'])).
% 0.41/0.64  thf('87', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.64  thf('88', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.64  thf('89', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('90', plain,
% 0.41/0.64      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.64         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.41/0.64          | ~ (v1_funct_1 @ X28)
% 0.41/0.64          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.41/0.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.41/0.64  thf('91', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.41/0.64          | ~ (v1_funct_1 @ sk_F))),
% 0.41/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.41/0.64  thf('92', plain, ((v1_funct_1 @ sk_F)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('93', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['91', '92'])).
% 0.41/0.64  thf('94', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.41/0.64      inference('simplify', [status(thm)], ['77'])).
% 0.41/0.64  thf('95', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('96', plain,
% 0.41/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.64         (~ (r1_xboole_0 @ X24 @ X25)
% 0.41/0.64          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.41/0.64          | ((k5_relset_1 @ X25 @ X27 @ X26 @ X24) = (k1_xboole_0)))),
% 0.41/0.64      inference('cnf', [status(esa)], [t55_relset_1])).
% 0.41/0.64  thf('97', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k5_relset_1 @ sk_D @ sk_B @ sk_F @ X0) = (k1_xboole_0))
% 0.41/0.64          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.41/0.64  thf('98', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('99', plain,
% 0.41/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.41/0.64          | ((k5_relset_1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.41/0.64      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.41/0.64  thf('100', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k5_relset_1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.41/0.64  thf('101', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         (((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0))
% 0.41/0.64          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('demod', [status(thm)], ['97', '100'])).
% 0.41/0.64  thf('102', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['94', '101'])).
% 0.41/0.64  thf('103', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('104', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('105', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('106', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('107', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64            = (sk_E))
% 0.41/0.64        | ~ (v1_funct_2 @ 
% 0.41/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_A))),
% 0.41/0.64      inference('demod', [status(thm)],
% 0.41/0.64                ['48', '49', '50', '51', '52', '55', '64', '69', '86', '87', 
% 0.41/0.64                 '88', '93', '102', '103', '104', '105', '106'])).
% 0.41/0.64  thf('108', plain,
% 0.41/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ~ (v1_funct_2 @ 
% 0.41/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64            = (sk_E))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify', [status(thm)], ['107'])).
% 0.41/0.64  thf('109', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64            = (sk_E))
% 0.41/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.64      inference('sup-', [status(thm)], ['30', '108'])).
% 0.41/0.64  thf('110', plain,
% 0.41/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64            = (sk_E))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify', [status(thm)], ['109'])).
% 0.41/0.64  thf('111', plain,
% 0.41/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64            != (sk_E))
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            != (sk_F)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('112', plain,
% 0.41/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64          != (sk_E)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64                = (sk_E))))),
% 0.41/0.64      inference('split', [status(esa)], ['111'])).
% 0.41/0.64  thf('113', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['91', '92'])).
% 0.41/0.64  thf('114', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.64  thf('115', plain,
% 0.41/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.41/0.64      inference('split', [status(esa)], ['111'])).
% 0.41/0.64  thf('116', plain,
% 0.41/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.41/0.64      inference('sup-', [status(thm)], ['114', '115'])).
% 0.41/0.64  thf('117', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.64  thf('118', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.64  thf('119', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.64  thf('120', plain,
% 0.41/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.41/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.41/0.64      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.41/0.64  thf('121', plain,
% 0.41/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.41/0.64          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.41/0.64      inference('sup-', [status(thm)], ['113', '120'])).
% 0.41/0.64  thf('122', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.64  thf('123', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['78', '85'])).
% 0.41/0.64  thf('124', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['94', '101'])).
% 0.41/0.64  thf('125', plain,
% 0.41/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.41/0.64      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.41/0.64  thf('126', plain,
% 0.41/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.41/0.64      inference('simplify', [status(thm)], ['125'])).
% 0.41/0.64  thf('127', plain,
% 0.41/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.64  thf('128', plain,
% 0.41/0.64      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.64  thf('129', plain,
% 0.41/0.64      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64         (k1_zfmisc_1 @ 
% 0.41/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.64  thf('130', plain,
% 0.41/0.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.64         ((v1_xboole_0 @ X32)
% 0.41/0.64          | (v1_xboole_0 @ X33)
% 0.41/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.41/0.64          | ~ (v1_funct_1 @ X35)
% 0.41/0.64          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.41/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.41/0.64          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.41/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X33)
% 0.41/0.64              = (X35))
% 0.41/0.64          | ~ (m1_subset_1 @ X38 @ 
% 0.41/0.64               (k1_zfmisc_1 @ 
% 0.41/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.41/0.64          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.41/0.64          | ~ (v1_funct_1 @ X38)
% 0.41/0.64          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.41/0.64              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.41/0.64                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.41/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.41/0.64          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.41/0.64          | ~ (v1_funct_1 @ X36)
% 0.41/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.41/0.64          | (v1_xboole_0 @ X37)
% 0.41/0.64          | (v1_xboole_0 @ X34))),
% 0.41/0.64      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.41/0.64  thf('131', plain,
% 0.41/0.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.64         ((v1_xboole_0 @ X34)
% 0.41/0.64          | (v1_xboole_0 @ X37)
% 0.41/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.41/0.64          | ~ (v1_funct_1 @ X36)
% 0.41/0.64          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.41/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.41/0.64          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.41/0.64              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.41/0.64                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.41/0.64          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.41/0.64          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.41/0.64               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.41/0.64          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.41/0.64               (k1_zfmisc_1 @ 
% 0.41/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.41/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.41/0.64              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X33) = (
% 0.41/0.64              X35))
% 0.41/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.41/0.64          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.41/0.64          | ~ (v1_funct_1 @ X35)
% 0.41/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.41/0.64          | (v1_xboole_0 @ X33)
% 0.41/0.64          | (v1_xboole_0 @ X32))),
% 0.41/0.64      inference('simplify', [status(thm)], ['130'])).
% 0.41/0.64  thf('132', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.41/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.41/0.64        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            = (sk_F))
% 0.41/0.64        | ~ (v1_funct_2 @ 
% 0.41/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.41/0.64            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.41/0.64        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.41/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.41/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.41/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_A))),
% 0.41/0.64      inference('sup-', [status(thm)], ['129', '131'])).
% 0.41/0.64  thf('133', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('134', plain, ((v1_funct_1 @ sk_F)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('135', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('136', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('137', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.64  thf('138', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.64  thf('139', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.64  thf('140', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['78', '85'])).
% 0.41/0.64  thf('141', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.41/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.64  thf('142', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.64  thf('143', plain,
% 0.41/0.64      (![X0 : $i]:
% 0.41/0.64         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.41/0.64      inference('demod', [status(thm)], ['91', '92'])).
% 0.41/0.64  thf('144', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.64      inference('sup-', [status(thm)], ['94', '101'])).
% 0.41/0.64  thf('145', plain,
% 0.41/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('146', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('147', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('148', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('149', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            = (sk_F))
% 0.41/0.64        | ~ (v1_funct_2 @ 
% 0.41/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_A))),
% 0.41/0.64      inference('demod', [status(thm)],
% 0.41/0.64                ['132', '133', '134', '135', '136', '137', '138', '139', 
% 0.41/0.64                 '140', '141', '142', '143', '144', '145', '146', '147', '148'])).
% 0.41/0.64  thf('150', plain,
% 0.41/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ~ (v1_funct_2 @ 
% 0.41/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.41/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            = (sk_F))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify', [status(thm)], ['149'])).
% 0.41/0.64  thf('151', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            = (sk_F))
% 0.41/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.41/0.64      inference('sup-', [status(thm)], ['128', '150'])).
% 0.41/0.64  thf('152', plain,
% 0.41/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            = (sk_F))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify', [status(thm)], ['151'])).
% 0.41/0.64  thf('153', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64            = (sk_F)))),
% 0.41/0.64      inference('sup-', [status(thm)], ['127', '152'])).
% 0.41/0.64  thf('154', plain,
% 0.41/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64          = (sk_F))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify', [status(thm)], ['153'])).
% 0.41/0.64  thf('155', plain,
% 0.41/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64          != (sk_F)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64                = (sk_F))))),
% 0.41/0.64      inference('split', [status(esa)], ['111'])).
% 0.41/0.64  thf('156', plain,
% 0.41/0.64      (((((sk_F) != (sk_F))
% 0.41/0.64         | (v1_xboole_0 @ sk_D)
% 0.41/0.64         | (v1_xboole_0 @ sk_C)
% 0.41/0.64         | (v1_xboole_0 @ sk_B)
% 0.41/0.64         | (v1_xboole_0 @ sk_A)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64                = (sk_F))))),
% 0.41/0.64      inference('sup-', [status(thm)], ['154', '155'])).
% 0.41/0.64  thf('157', plain,
% 0.41/0.64      ((((v1_xboole_0 @ sk_A)
% 0.41/0.64         | (v1_xboole_0 @ sk_B)
% 0.41/0.64         | (v1_xboole_0 @ sk_C)
% 0.41/0.64         | (v1_xboole_0 @ sk_D)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64                = (sk_F))))),
% 0.41/0.64      inference('simplify', [status(thm)], ['156'])).
% 0.41/0.64  thf('158', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('159', plain,
% 0.41/0.64      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64                = (sk_F))))),
% 0.41/0.64      inference('sup-', [status(thm)], ['157', '158'])).
% 0.41/0.64  thf('160', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('161', plain,
% 0.41/0.64      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64                = (sk_F))))),
% 0.41/0.64      inference('clc', [status(thm)], ['159', '160'])).
% 0.41/0.64  thf('162', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('163', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_B))
% 0.41/0.64         <= (~
% 0.41/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64                = (sk_F))))),
% 0.41/0.64      inference('clc', [status(thm)], ['161', '162'])).
% 0.41/0.64  thf('164', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('165', plain,
% 0.41/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64          = (sk_F)))),
% 0.41/0.64      inference('sup-', [status(thm)], ['163', '164'])).
% 0.41/0.64  thf('166', plain,
% 0.41/0.64      (~
% 0.41/0.64       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64          = (sk_E))) | 
% 0.41/0.64       ~
% 0.41/0.64       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.41/0.64          = (sk_F))) | 
% 0.41/0.64       ~
% 0.41/0.64       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.41/0.64          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.41/0.64             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.41/0.64      inference('split', [status(esa)], ['111'])).
% 0.41/0.64  thf('167', plain,
% 0.41/0.64      (~
% 0.41/0.64       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64          = (sk_E)))),
% 0.41/0.64      inference('sat_resolution*', [status(thm)], ['126', '165', '166'])).
% 0.41/0.64  thf('168', plain,
% 0.41/0.64      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.41/0.64         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.41/0.64         != (sk_E))),
% 0.41/0.64      inference('simpl_trail', [status(thm)], ['112', '167'])).
% 0.41/0.64  thf('169', plain,
% 0.41/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify_reflect-', [status(thm)], ['110', '168'])).
% 0.41/0.64  thf('170', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_D)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_A))),
% 0.41/0.64      inference('sup-', [status(thm)], ['15', '169'])).
% 0.41/0.64  thf('171', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_A)
% 0.41/0.64        | (v1_xboole_0 @ sk_B)
% 0.41/0.64        | (v1_xboole_0 @ sk_C)
% 0.41/0.64        | (v1_xboole_0 @ sk_D))),
% 0.41/0.64      inference('simplify', [status(thm)], ['170'])).
% 0.41/0.64  thf('172', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('173', plain,
% 0.41/0.64      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.41/0.64      inference('sup-', [status(thm)], ['171', '172'])).
% 0.41/0.64  thf('174', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('175', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.41/0.64      inference('clc', [status(thm)], ['173', '174'])).
% 0.41/0.64  thf('176', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.64  thf('177', plain, ((v1_xboole_0 @ sk_B)),
% 0.41/0.64      inference('clc', [status(thm)], ['175', '176'])).
% 0.41/0.64  thf('178', plain, ($false), inference('demod', [status(thm)], ['0', '177'])).
% 0.41/0.64  
% 0.41/0.64  % SZS output end Refutation
% 0.41/0.64  
% 0.41/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
