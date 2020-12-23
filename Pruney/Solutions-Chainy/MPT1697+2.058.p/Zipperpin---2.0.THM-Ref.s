%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lH0Ffp3b6

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:02 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  249 (1139 expanded)
%              Number of leaves         :   42 ( 351 expanded)
%              Depth                    :   34
%              Number of atoms          : 3650 (43258 expanded)
%              Number of equality atoms :  128 (1437 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('67',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['69','70'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X10 @ X8 ) @ X9 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k7_relat_1 @ sk_E @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['61','62'])).

thf('76',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('78',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_E ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('79',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('80',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['61','62'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_E ) @ sk_D ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
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

thf('83',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['87','88'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('90',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['61','62'])).

thf('93',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('97',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['60','63'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('102',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('103',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X10 @ X8 ) @ X9 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['61','62'])).

thf('107',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('109',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('110',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('117',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('122',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('125',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['120','121'])).

thf('127',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','95','100','107','108','109','114','127','128','129','130','131'])).

thf('133',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('137',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('139',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['134'])).

thf('140',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('142',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf('144',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('148',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('149',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('150',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('153',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('154',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('155',plain,(
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

thf('156',plain,(
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
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
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
    inference('sup-',[status(thm)],['154','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('163',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('165',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('167',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('169',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('170',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
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
    inference(demod,[status(thm)],['157','158','159','160','161','162','163','164','165','166','167','168','169','170','171','172','173'])).

thf('175',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
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
    inference('sup-',[status(thm)],['153','175'])).

thf('177',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
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
    inference('sup-',[status(thm)],['152','177'])).

thf('179',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['134'])).

thf('181',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['134'])).

thf('192',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['151','190','191'])).

thf('193',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['135','192'])).

thf('194',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['133','193'])).

thf('195',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','194'])).

thf('196',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','196'])).

thf('198',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    $false ),
    inference(demod,[status(thm)],['0','204'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lH0Ffp3b6
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.12/2.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.29  % Solved by: fo/fo7.sh
% 2.12/2.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.29  % done 896 iterations in 1.836s
% 2.12/2.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.29  % SZS output start Refutation
% 2.12/2.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.12/2.29  thf(sk_B_type, type, sk_B: $i).
% 2.12/2.29  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.12/2.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.12/2.29  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.12/2.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.12/2.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.12/2.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.12/2.29  thf(sk_E_type, type, sk_E: $i).
% 2.12/2.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.12/2.29  thf(sk_D_type, type, sk_D: $i).
% 2.12/2.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.12/2.29  thf(sk_C_type, type, sk_C: $i).
% 2.12/2.29  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.29  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 2.12/2.29  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 2.12/2.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.12/2.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.12/2.29  thf(sk_F_type, type, sk_F: $i).
% 2.12/2.29  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.12/2.29  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.12/2.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.12/2.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.12/2.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.12/2.29  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.12/2.29  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.12/2.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.12/2.29  thf(t6_tmap_1, conjecture,
% 2.12/2.29    (![A:$i]:
% 2.12/2.29     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.12/2.29       ( ![B:$i]:
% 2.12/2.29         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.12/2.29           ( ![C:$i]:
% 2.12/2.29             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 2.12/2.29                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.12/2.29               ( ![D:$i]:
% 2.12/2.29                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 2.12/2.29                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.12/2.29                   ( ( r1_subset_1 @ C @ D ) =>
% 2.12/2.29                     ( ![E:$i]:
% 2.12/2.29                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 2.12/2.29                           ( m1_subset_1 @
% 2.12/2.29                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 2.12/2.29                         ( ![F:$i]:
% 2.12/2.29                           ( ( ( v1_funct_1 @ F ) & 
% 2.12/2.29                               ( v1_funct_2 @ F @ D @ B ) & 
% 2.12/2.29                               ( m1_subset_1 @
% 2.12/2.29                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.12/2.29                             ( ( ( k2_partfun1 @
% 2.12/2.29                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 2.12/2.29                                 ( k2_partfun1 @
% 2.12/2.29                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 2.12/2.29                               ( ( k2_partfun1 @
% 2.12/2.29                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.12/2.29                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 2.12/2.29                                 ( E ) ) & 
% 2.12/2.29                               ( ( k2_partfun1 @
% 2.12/2.29                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.12/2.29                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 2.12/2.29                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.12/2.29  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.29    (~( ![A:$i]:
% 2.12/2.29        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.12/2.29          ( ![B:$i]:
% 2.12/2.29            ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.12/2.29              ( ![C:$i]:
% 2.12/2.29                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 2.12/2.29                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.12/2.29                  ( ![D:$i]:
% 2.12/2.29                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 2.12/2.29                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.12/2.29                      ( ( r1_subset_1 @ C @ D ) =>
% 2.12/2.29                        ( ![E:$i]:
% 2.12/2.29                          ( ( ( v1_funct_1 @ E ) & 
% 2.12/2.29                              ( v1_funct_2 @ E @ C @ B ) & 
% 2.12/2.29                              ( m1_subset_1 @
% 2.12/2.29                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 2.12/2.29                            ( ![F:$i]:
% 2.12/2.29                              ( ( ( v1_funct_1 @ F ) & 
% 2.12/2.29                                  ( v1_funct_2 @ F @ D @ B ) & 
% 2.12/2.29                                  ( m1_subset_1 @
% 2.12/2.29                                    F @ 
% 2.12/2.29                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.12/2.29                                ( ( ( k2_partfun1 @
% 2.12/2.29                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 2.12/2.29                                    ( k2_partfun1 @
% 2.12/2.29                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 2.12/2.29                                  ( ( k2_partfun1 @
% 2.12/2.29                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.12/2.29                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 2.12/2.29                                    ( E ) ) & 
% 2.12/2.29                                  ( ( k2_partfun1 @
% 2.12/2.29                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.12/2.29                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 2.12/2.29                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.12/2.29    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 2.12/2.29  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('2', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('3', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf(dt_k1_tmap_1, axiom,
% 2.12/2.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.12/2.29     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.12/2.29         ( ~( v1_xboole_0 @ C ) ) & 
% 2.12/2.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 2.12/2.29         ( ~( v1_xboole_0 @ D ) ) & 
% 2.12/2.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 2.12/2.29         ( v1_funct_2 @ E @ C @ B ) & 
% 2.12/2.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.12/2.29         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 2.12/2.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.12/2.29       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.12/2.29         ( v1_funct_2 @
% 2.12/2.29           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.12/2.29           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 2.12/2.29         ( m1_subset_1 @
% 2.12/2.29           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.12/2.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 2.12/2.29  thf('4', plain,
% 2.12/2.29      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.12/2.29          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 2.12/2.29          | ~ (v1_funct_1 @ X39)
% 2.12/2.29          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 2.12/2.29          | (v1_xboole_0 @ X42)
% 2.12/2.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 2.12/2.29          | (v1_xboole_0 @ X40)
% 2.12/2.29          | (v1_xboole_0 @ X41)
% 2.12/2.29          | (v1_xboole_0 @ X43)
% 2.12/2.29          | ~ (v1_funct_1 @ X44)
% 2.12/2.29          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 2.12/2.29          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 2.12/2.29          | (v1_funct_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44)))),
% 2.12/2.29      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 2.12/2.29  thf('5', plain,
% 2.12/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.29         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.12/2.29          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.12/2.29          | ~ (v1_funct_1 @ X0)
% 2.12/2.29          | (v1_xboole_0 @ X2)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 2.12/2.29          | (v1_xboole_0 @ X1)
% 2.12/2.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 2.12/2.29          | ~ (v1_funct_1 @ sk_E)
% 2.12/2.29          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 2.12/2.29      inference('sup-', [status(thm)], ['3', '4'])).
% 2.12/2.29  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('8', plain,
% 2.12/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.29         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.12/2.29          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.12/2.29          | ~ (v1_funct_1 @ X0)
% 2.12/2.29          | (v1_xboole_0 @ X2)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 2.12/2.29          | (v1_xboole_0 @ X1)
% 2.12/2.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 2.12/2.29      inference('demod', [status(thm)], ['5', '6', '7'])).
% 2.12/2.29  thf('9', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_D)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (v1_funct_1 @ sk_F)
% 2.12/2.29          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.12/2.29          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 2.12/2.29      inference('sup-', [status(thm)], ['2', '8'])).
% 2.12/2.29  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('12', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_D)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 2.12/2.29      inference('demod', [status(thm)], ['9', '10', '11'])).
% 2.12/2.29  thf('13', plain,
% 2.12/2.29      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.29        | (v1_xboole_0 @ sk_D))),
% 2.12/2.29      inference('sup-', [status(thm)], ['1', '12'])).
% 2.12/2.29  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('15', plain,
% 2.12/2.29      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | (v1_xboole_0 @ sk_D))),
% 2.12/2.29      inference('demod', [status(thm)], ['13', '14'])).
% 2.12/2.29  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('17', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('18', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('19', plain,
% 2.12/2.29      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.12/2.29          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 2.12/2.29          | ~ (v1_funct_1 @ X39)
% 2.12/2.29          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 2.12/2.29          | (v1_xboole_0 @ X42)
% 2.12/2.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 2.12/2.29          | (v1_xboole_0 @ X40)
% 2.12/2.29          | (v1_xboole_0 @ X41)
% 2.12/2.29          | (v1_xboole_0 @ X43)
% 2.12/2.29          | ~ (v1_funct_1 @ X44)
% 2.12/2.29          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 2.12/2.29          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 2.12/2.29          | (v1_funct_2 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 2.12/2.29             (k4_subset_1 @ X43 @ X40 @ X42) @ X41))),
% 2.12/2.29      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 2.12/2.29  thf('20', plain,
% 2.12/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.29         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 2.12/2.29           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 2.12/2.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.12/2.29          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.12/2.29          | ~ (v1_funct_1 @ X2)
% 2.12/2.29          | (v1_xboole_0 @ X1)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.12/2.29          | ~ (v1_funct_1 @ sk_E)
% 2.12/2.29          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 2.12/2.29      inference('sup-', [status(thm)], ['18', '19'])).
% 2.12/2.29  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('23', plain,
% 2.12/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.29         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 2.12/2.29           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 2.12/2.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.12/2.29          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.12/2.29          | ~ (v1_funct_1 @ X2)
% 2.12/2.29          | (v1_xboole_0 @ X1)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 2.12/2.29      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.12/2.29  thf('24', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_D)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (v1_funct_1 @ sk_F)
% 2.12/2.29          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.12/2.29          | (v1_funct_2 @ 
% 2.12/2.29             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 2.12/2.29      inference('sup-', [status(thm)], ['17', '23'])).
% 2.12/2.29  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('27', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_D)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | (v1_funct_2 @ 
% 2.12/2.29             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 2.12/2.29      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.12/2.29  thf('28', plain,
% 2.12/2.29      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.29        | (v1_xboole_0 @ sk_D))),
% 2.12/2.29      inference('sup-', [status(thm)], ['16', '27'])).
% 2.12/2.29  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('30', plain,
% 2.12/2.29      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | (v1_xboole_0 @ sk_D))),
% 2.12/2.29      inference('demod', [status(thm)], ['28', '29'])).
% 2.12/2.29  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('32', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('33', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('34', plain,
% 2.12/2.29      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.12/2.29          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 2.12/2.29          | ~ (v1_funct_1 @ X39)
% 2.12/2.29          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 2.12/2.29          | (v1_xboole_0 @ X42)
% 2.12/2.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 2.12/2.29          | (v1_xboole_0 @ X40)
% 2.12/2.29          | (v1_xboole_0 @ X41)
% 2.12/2.29          | (v1_xboole_0 @ X43)
% 2.12/2.29          | ~ (v1_funct_1 @ X44)
% 2.12/2.29          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 2.12/2.29          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 2.12/2.29          | (m1_subset_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 2.12/2.29             (k1_zfmisc_1 @ 
% 2.12/2.29              (k2_zfmisc_1 @ (k4_subset_1 @ X43 @ X40 @ X42) @ X41))))),
% 2.12/2.29      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 2.12/2.29  thf('35', plain,
% 2.12/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.29         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 2.12/2.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 2.12/2.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.12/2.29          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.12/2.29          | ~ (v1_funct_1 @ X2)
% 2.12/2.29          | (v1_xboole_0 @ X1)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.12/2.29          | ~ (v1_funct_1 @ sk_E)
% 2.12/2.29          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 2.12/2.29      inference('sup-', [status(thm)], ['33', '34'])).
% 2.12/2.29  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('38', plain,
% 2.12/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.29         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 2.12/2.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 2.12/2.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.12/2.29          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.12/2.29          | ~ (v1_funct_1 @ X2)
% 2.12/2.29          | (v1_xboole_0 @ X1)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 2.12/2.29      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.12/2.29  thf('39', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_D)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | ~ (v1_funct_1 @ sk_F)
% 2.12/2.29          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.12/2.29          | (m1_subset_1 @ 
% 2.12/2.29             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29             (k1_zfmisc_1 @ 
% 2.12/2.29              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 2.12/2.29      inference('sup-', [status(thm)], ['32', '38'])).
% 2.12/2.29  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('42', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_D)
% 2.12/2.29          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 2.12/2.29          | (v1_xboole_0 @ sk_C)
% 2.12/2.29          | (v1_xboole_0 @ sk_B)
% 2.12/2.29          | (v1_xboole_0 @ X0)
% 2.12/2.29          | (m1_subset_1 @ 
% 2.12/2.29             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29             (k1_zfmisc_1 @ 
% 2.12/2.29              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 2.12/2.29      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.12/2.29  thf('43', plain,
% 2.12/2.29      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29         (k1_zfmisc_1 @ 
% 2.12/2.29          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.29        | (v1_xboole_0 @ sk_D))),
% 2.12/2.29      inference('sup-', [status(thm)], ['31', '42'])).
% 2.12/2.29  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('45', plain,
% 2.12/2.29      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29         (k1_zfmisc_1 @ 
% 2.12/2.29          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | (v1_xboole_0 @ sk_D))),
% 2.12/2.29      inference('demod', [status(thm)], ['43', '44'])).
% 2.12/2.29  thf(d1_tmap_1, axiom,
% 2.12/2.29    (![A:$i]:
% 2.12/2.29     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.12/2.29       ( ![B:$i]:
% 2.12/2.29         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.12/2.29           ( ![C:$i]:
% 2.12/2.29             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 2.12/2.29                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.12/2.29               ( ![D:$i]:
% 2.12/2.29                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 2.12/2.29                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.12/2.29                   ( ![E:$i]:
% 2.12/2.29                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 2.12/2.29                         ( m1_subset_1 @
% 2.12/2.29                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 2.12/2.29                       ( ![F:$i]:
% 2.12/2.29                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 2.12/2.29                             ( m1_subset_1 @
% 2.12/2.29                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.12/2.29                           ( ( ( k2_partfun1 @
% 2.12/2.29                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 2.12/2.29                               ( k2_partfun1 @
% 2.12/2.29                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 2.12/2.29                             ( ![G:$i]:
% 2.12/2.29                               ( ( ( v1_funct_1 @ G ) & 
% 2.12/2.29                                   ( v1_funct_2 @
% 2.12/2.29                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 2.12/2.29                                   ( m1_subset_1 @
% 2.12/2.29                                     G @ 
% 2.12/2.29                                     ( k1_zfmisc_1 @
% 2.12/2.29                                       ( k2_zfmisc_1 @
% 2.12/2.29                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 2.12/2.29                                 ( ( ( G ) =
% 2.12/2.29                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 2.12/2.29                                   ( ( ( k2_partfun1 @
% 2.12/2.29                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 2.12/2.29                                         C ) =
% 2.12/2.29                                       ( E ) ) & 
% 2.12/2.29                                     ( ( k2_partfun1 @
% 2.12/2.29                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 2.12/2.29                                         D ) =
% 2.12/2.29                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.12/2.29  thf('46', plain,
% 2.12/2.29      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.12/2.29         ((v1_xboole_0 @ X32)
% 2.12/2.29          | (v1_xboole_0 @ X33)
% 2.12/2.29          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 2.12/2.29          | ~ (v1_funct_1 @ X35)
% 2.12/2.29          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 2.12/2.29          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.12/2.29          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 2.12/2.29          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X37)
% 2.12/2.29              = (X36))
% 2.12/2.29          | ~ (m1_subset_1 @ X38 @ 
% 2.12/2.29               (k1_zfmisc_1 @ 
% 2.12/2.29                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 2.12/2.29          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 2.12/2.29          | ~ (v1_funct_1 @ X38)
% 2.12/2.29          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 2.12/2.29              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 2.12/2.29                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 2.12/2.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 2.12/2.29          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 2.12/2.29          | ~ (v1_funct_1 @ X36)
% 2.12/2.29          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 2.12/2.29          | (v1_xboole_0 @ X37)
% 2.12/2.29          | (v1_xboole_0 @ X34))),
% 2.12/2.29      inference('cnf', [status(esa)], [d1_tmap_1])).
% 2.12/2.29  thf('47', plain,
% 2.12/2.29      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.12/2.29         ((v1_xboole_0 @ X34)
% 2.12/2.29          | (v1_xboole_0 @ X37)
% 2.12/2.29          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 2.12/2.29          | ~ (v1_funct_1 @ X36)
% 2.12/2.29          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 2.12/2.29          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 2.12/2.29          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 2.12/2.29              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 2.12/2.29                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 2.12/2.29          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 2.12/2.29          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 2.12/2.29               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 2.12/2.29          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 2.12/2.29               (k1_zfmisc_1 @ 
% 2.12/2.29                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 2.12/2.29          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 2.12/2.29              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X37) = (
% 2.12/2.29              X36))
% 2.12/2.29          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.12/2.29          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 2.12/2.29          | ~ (v1_funct_1 @ X35)
% 2.12/2.29          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 2.12/2.29          | (v1_xboole_0 @ X33)
% 2.12/2.29          | (v1_xboole_0 @ X32))),
% 2.12/2.29      inference('simplify', [status(thm)], ['46'])).
% 2.12/2.29  thf('48', plain,
% 2.12/2.29      (((v1_xboole_0 @ sk_D)
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_A)
% 2.12/2.29        | (v1_xboole_0 @ sk_B)
% 2.12/2.29        | (v1_xboole_0 @ sk_D)
% 2.12/2.29        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.29        | ~ (v1_funct_1 @ sk_F)
% 2.12/2.29        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.12/2.29        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 2.12/2.29        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.29            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.29            = (sk_E))
% 2.12/2.29        | ~ (v1_funct_2 @ 
% 2.12/2.29             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.29             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.29        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.29        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.29            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.29            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.29                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 2.12/2.29        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 2.12/2.29        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 2.12/2.29        | ~ (v1_funct_1 @ sk_E)
% 2.12/2.29        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.29        | (v1_xboole_0 @ sk_C)
% 2.12/2.29        | (v1_xboole_0 @ sk_A))),
% 2.12/2.29      inference('sup-', [status(thm)], ['45', '47'])).
% 2.12/2.29  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('52', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf(redefinition_k9_subset_1, axiom,
% 2.12/2.29    (![A:$i,B:$i,C:$i]:
% 2.12/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.12/2.29       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.12/2.29  thf('54', plain,
% 2.12/2.29      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.12/2.29         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 2.12/2.29          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 2.12/2.29      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.12/2.29  thf('55', plain,
% 2.12/2.29      (![X0 : $i]:
% 2.12/2.29         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.12/2.29      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.29  thf('56', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.29  thf(cc2_relset_1, axiom,
% 2.12/2.29    (![A:$i,B:$i,C:$i]:
% 2.12/2.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.12/2.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.12/2.29  thf('57', plain,
% 2.12/2.29      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.12/2.29         ((v4_relat_1 @ X20 @ X21)
% 2.12/2.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.12/2.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.12/2.29  thf('58', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 2.12/2.29      inference('sup-', [status(thm)], ['56', '57'])).
% 2.12/2.29  thf(t209_relat_1, axiom,
% 2.12/2.29    (![A:$i,B:$i]:
% 2.12/2.29     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.12/2.29       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.12/2.29  thf('59', plain,
% 2.12/2.29      (![X11 : $i, X12 : $i]:
% 2.12/2.29         (((X11) = (k7_relat_1 @ X11 @ X12))
% 2.12/2.29          | ~ (v4_relat_1 @ X11 @ X12)
% 2.12/2.29          | ~ (v1_relat_1 @ X11))),
% 2.12/2.29      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.12/2.29  thf('60', plain,
% 2.12/2.29      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C)))),
% 2.12/2.29      inference('sup-', [status(thm)], ['58', '59'])).
% 2.12/2.29  thf('61', plain,
% 2.12/2.29      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf(cc1_relset_1, axiom,
% 2.12/2.30    (![A:$i,B:$i,C:$i]:
% 2.12/2.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.12/2.30       ( v1_relat_1 @ C ) ))).
% 2.12/2.30  thf('62', plain,
% 2.12/2.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.12/2.30         ((v1_relat_1 @ X17)
% 2.12/2.30          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.12/2.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.12/2.30  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 2.12/2.30      inference('sup-', [status(thm)], ['61', '62'])).
% 2.12/2.30  thf('64', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C))),
% 2.12/2.30      inference('demod', [status(thm)], ['60', '63'])).
% 2.12/2.30  thf('65', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf(redefinition_r1_subset_1, axiom,
% 2.12/2.30    (![A:$i,B:$i]:
% 2.12/2.30     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 2.12/2.30       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 2.12/2.30  thf('66', plain,
% 2.12/2.30      (![X15 : $i, X16 : $i]:
% 2.12/2.30         ((v1_xboole_0 @ X15)
% 2.12/2.30          | (v1_xboole_0 @ X16)
% 2.12/2.30          | (r1_xboole_0 @ X15 @ X16)
% 2.12/2.30          | ~ (r1_subset_1 @ X15 @ X16))),
% 2.12/2.30      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 2.12/2.30  thf('67', plain,
% 2.12/2.30      (((r1_xboole_0 @ sk_C @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C))),
% 2.12/2.30      inference('sup-', [status(thm)], ['65', '66'])).
% 2.12/2.30  thf('68', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('69', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('clc', [status(thm)], ['67', '68'])).
% 2.12/2.30  thf('70', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('71', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 2.12/2.30      inference('clc', [status(thm)], ['69', '70'])).
% 2.12/2.30  thf(t207_relat_1, axiom,
% 2.12/2.30    (![A:$i,B:$i,C:$i]:
% 2.12/2.30     ( ( v1_relat_1 @ C ) =>
% 2.12/2.30       ( ( r1_xboole_0 @ A @ B ) =>
% 2.12/2.30         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 2.12/2.30  thf('72', plain,
% 2.12/2.30      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.12/2.30         (~ (r1_xboole_0 @ X8 @ X9)
% 2.12/2.30          | ~ (v1_relat_1 @ X10)
% 2.12/2.30          | ((k7_relat_1 @ (k7_relat_1 @ X10 @ X8) @ X9) = (k1_xboole_0)))),
% 2.12/2.30      inference('cnf', [status(esa)], [t207_relat_1])).
% 2.12/2.30  thf('73', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_D) = (k1_xboole_0))
% 2.12/2.30          | ~ (v1_relat_1 @ X0))),
% 2.12/2.30      inference('sup-', [status(thm)], ['71', '72'])).
% 2.12/2.30  thf('74', plain,
% 2.12/2.30      ((((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E))),
% 2.12/2.30      inference('sup+', [status(thm)], ['64', '73'])).
% 2.12/2.30  thf('75', plain, ((v1_relat_1 @ sk_E)),
% 2.12/2.30      inference('sup-', [status(thm)], ['61', '62'])).
% 2.12/2.30  thf('76', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['74', '75'])).
% 2.12/2.30  thf(t90_relat_1, axiom,
% 2.12/2.30    (![A:$i,B:$i]:
% 2.12/2.30     ( ( v1_relat_1 @ B ) =>
% 2.12/2.30       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 2.12/2.30         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.12/2.30  thf('77', plain,
% 2.12/2.30      (![X13 : $i, X14 : $i]:
% 2.12/2.30         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 2.12/2.30            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 2.12/2.30          | ~ (v1_relat_1 @ X13))),
% 2.12/2.30      inference('cnf', [status(esa)], [t90_relat_1])).
% 2.12/2.30  thf('78', plain,
% 2.12/2.30      ((((k1_relat_1 @ k1_xboole_0)
% 2.12/2.30          = (k3_xboole_0 @ (k1_relat_1 @ sk_E) @ sk_D))
% 2.12/2.30        | ~ (v1_relat_1 @ sk_E))),
% 2.12/2.30      inference('sup+', [status(thm)], ['76', '77'])).
% 2.12/2.30  thf(t60_relat_1, axiom,
% 2.12/2.30    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.12/2.30     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.12/2.30  thf('79', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.12/2.30  thf('80', plain, ((v1_relat_1 @ sk_E)),
% 2.12/2.30      inference('sup-', [status(thm)], ['61', '62'])).
% 2.12/2.30  thf('81', plain,
% 2.12/2.30      (((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_E) @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['78', '79', '80'])).
% 2.12/2.30  thf('82', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf(cc5_funct_2, axiom,
% 2.12/2.30    (![A:$i,B:$i]:
% 2.12/2.30     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.12/2.30       ( ![C:$i]:
% 2.12/2.30         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.12/2.30           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 2.12/2.30             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 2.12/2.30  thf('83', plain,
% 2.12/2.30      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.12/2.30         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 2.12/2.30          | (v1_partfun1 @ X23 @ X24)
% 2.12/2.30          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 2.12/2.30          | ~ (v1_funct_1 @ X23)
% 2.12/2.30          | (v1_xboole_0 @ X25))),
% 2.12/2.30      inference('cnf', [status(esa)], [cc5_funct_2])).
% 2.12/2.30  thf('84', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_B)
% 2.12/2.30        | ~ (v1_funct_1 @ sk_E)
% 2.12/2.30        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 2.12/2.30        | (v1_partfun1 @ sk_E @ sk_C))),
% 2.12/2.30      inference('sup-', [status(thm)], ['82', '83'])).
% 2.12/2.30  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('86', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('87', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 2.12/2.30      inference('demod', [status(thm)], ['84', '85', '86'])).
% 2.12/2.30  thf('88', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('89', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 2.12/2.30      inference('clc', [status(thm)], ['87', '88'])).
% 2.12/2.30  thf(d4_partfun1, axiom,
% 2.12/2.30    (![A:$i,B:$i]:
% 2.12/2.30     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.12/2.30       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.12/2.30  thf('90', plain,
% 2.12/2.30      (![X26 : $i, X27 : $i]:
% 2.12/2.30         (~ (v1_partfun1 @ X27 @ X26)
% 2.12/2.30          | ((k1_relat_1 @ X27) = (X26))
% 2.12/2.30          | ~ (v4_relat_1 @ X27 @ X26)
% 2.12/2.30          | ~ (v1_relat_1 @ X27))),
% 2.12/2.30      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.12/2.30  thf('91', plain,
% 2.12/2.30      ((~ (v1_relat_1 @ sk_E)
% 2.12/2.30        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 2.12/2.30        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 2.12/2.30      inference('sup-', [status(thm)], ['89', '90'])).
% 2.12/2.30  thf('92', plain, ((v1_relat_1 @ sk_E)),
% 2.12/2.30      inference('sup-', [status(thm)], ['61', '62'])).
% 2.12/2.30  thf('93', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 2.12/2.30      inference('sup-', [status(thm)], ['56', '57'])).
% 2.12/2.30  thf('94', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 2.12/2.30      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.12/2.30  thf('95', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['81', '94'])).
% 2.12/2.30  thf('96', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf(redefinition_k2_partfun1, axiom,
% 2.12/2.30    (![A:$i,B:$i,C:$i,D:$i]:
% 2.12/2.30     ( ( ( v1_funct_1 @ C ) & 
% 2.12/2.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.12/2.30       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 2.12/2.30  thf('97', plain,
% 2.12/2.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.12/2.30         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.12/2.30          | ~ (v1_funct_1 @ X28)
% 2.12/2.30          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 2.12/2.30      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 2.12/2.30  thf('98', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 2.12/2.30          | ~ (v1_funct_1 @ sk_E))),
% 2.12/2.30      inference('sup-', [status(thm)], ['96', '97'])).
% 2.12/2.30  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('100', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 2.12/2.30      inference('demod', [status(thm)], ['98', '99'])).
% 2.12/2.30  thf('101', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C))),
% 2.12/2.30      inference('demod', [status(thm)], ['60', '63'])).
% 2.12/2.30  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.12/2.30  thf('102', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 2.12/2.30      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.12/2.30  thf('103', plain,
% 2.12/2.30      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.12/2.30         (~ (r1_xboole_0 @ X8 @ X9)
% 2.12/2.30          | ~ (v1_relat_1 @ X10)
% 2.12/2.30          | ((k7_relat_1 @ (k7_relat_1 @ X10 @ X8) @ X9) = (k1_xboole_0)))),
% 2.12/2.30      inference('cnf', [status(esa)], [t207_relat_1])).
% 2.12/2.30  thf('104', plain,
% 2.12/2.30      (![X0 : $i, X1 : $i]:
% 2.12/2.30         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 2.12/2.30          | ~ (v1_relat_1 @ X1))),
% 2.12/2.30      inference('sup-', [status(thm)], ['102', '103'])).
% 2.12/2.30  thf('105', plain,
% 2.12/2.30      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 2.12/2.30        | ~ (v1_relat_1 @ sk_E))),
% 2.12/2.30      inference('sup+', [status(thm)], ['101', '104'])).
% 2.12/2.30  thf('106', plain, ((v1_relat_1 @ sk_E)),
% 2.12/2.30      inference('sup-', [status(thm)], ['61', '62'])).
% 2.12/2.30  thf('107', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['105', '106'])).
% 2.12/2.30  thf('108', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.12/2.30      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.30  thf('109', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['81', '94'])).
% 2.12/2.30  thf('110', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('111', plain,
% 2.12/2.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.12/2.30         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.12/2.30          | ~ (v1_funct_1 @ X28)
% 2.12/2.30          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 2.12/2.30      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 2.12/2.30  thf('112', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 2.12/2.30          | ~ (v1_funct_1 @ sk_F))),
% 2.12/2.30      inference('sup-', [status(thm)], ['110', '111'])).
% 2.12/2.30  thf('113', plain, ((v1_funct_1 @ sk_F)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('114', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 2.12/2.30      inference('demod', [status(thm)], ['112', '113'])).
% 2.12/2.30  thf('115', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('116', plain,
% 2.12/2.30      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.12/2.30         ((v4_relat_1 @ X20 @ X21)
% 2.12/2.30          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.12/2.30      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.12/2.30  thf('117', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 2.12/2.30      inference('sup-', [status(thm)], ['115', '116'])).
% 2.12/2.30  thf('118', plain,
% 2.12/2.30      (![X11 : $i, X12 : $i]:
% 2.12/2.30         (((X11) = (k7_relat_1 @ X11 @ X12))
% 2.12/2.30          | ~ (v4_relat_1 @ X11 @ X12)
% 2.12/2.30          | ~ (v1_relat_1 @ X11))),
% 2.12/2.30      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.12/2.30  thf('119', plain,
% 2.12/2.30      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 2.12/2.30      inference('sup-', [status(thm)], ['117', '118'])).
% 2.12/2.30  thf('120', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('121', plain,
% 2.12/2.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.12/2.30         ((v1_relat_1 @ X17)
% 2.12/2.30          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.12/2.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.12/2.30  thf('122', plain, ((v1_relat_1 @ sk_F)),
% 2.12/2.30      inference('sup-', [status(thm)], ['120', '121'])).
% 2.12/2.30  thf('123', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['119', '122'])).
% 2.12/2.30  thf('124', plain,
% 2.12/2.30      (![X0 : $i, X1 : $i]:
% 2.12/2.30         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 2.12/2.30          | ~ (v1_relat_1 @ X1))),
% 2.12/2.30      inference('sup-', [status(thm)], ['102', '103'])).
% 2.12/2.30  thf('125', plain,
% 2.12/2.30      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 2.12/2.30        | ~ (v1_relat_1 @ sk_F))),
% 2.12/2.30      inference('sup+', [status(thm)], ['123', '124'])).
% 2.12/2.30  thf('126', plain, ((v1_relat_1 @ sk_F)),
% 2.12/2.30      inference('sup-', [status(thm)], ['120', '121'])).
% 2.12/2.30  thf('127', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['125', '126'])).
% 2.12/2.30  thf('128', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('129', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('131', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('132', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30            = (sk_E))
% 2.12/2.30        | ~ (v1_funct_2 @ 
% 2.12/2.30             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ((k1_xboole_0) != (k1_xboole_0))
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_A))),
% 2.12/2.30      inference('demod', [status(thm)],
% 2.12/2.30                ['48', '49', '50', '51', '52', '55', '95', '100', '107', 
% 2.12/2.30                 '108', '109', '114', '127', '128', '129', '130', '131'])).
% 2.12/2.30  thf('133', plain,
% 2.12/2.30      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ~ (v1_funct_2 @ 
% 2.12/2.30             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30            = (sk_E))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify', [status(thm)], ['132'])).
% 2.12/2.30  thf('134', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30            != (sk_E))
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            != (sk_F)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('135', plain,
% 2.12/2.30      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30          != (sk_E)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30                = (sk_E))))),
% 2.12/2.30      inference('split', [status(esa)], ['134'])).
% 2.12/2.30  thf('136', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 2.12/2.30      inference('demod', [status(thm)], ['112', '113'])).
% 2.12/2.30  thf('137', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['81', '94'])).
% 2.12/2.30  thf('138', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.12/2.30      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.30  thf('139', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('split', [status(esa)], ['134'])).
% 2.12/2.30  thf('140', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('sup-', [status(thm)], ['138', '139'])).
% 2.12/2.30  thf('141', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.12/2.30      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.30  thf('142', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 2.12/2.30          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('demod', [status(thm)], ['140', '141'])).
% 2.12/2.30  thf('143', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 2.12/2.30          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('sup-', [status(thm)], ['137', '142'])).
% 2.12/2.30  thf('144', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['81', '94'])).
% 2.12/2.30  thf('145', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 2.12/2.30          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('demod', [status(thm)], ['143', '144'])).
% 2.12/2.30  thf('146', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 2.12/2.30          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('sup-', [status(thm)], ['136', '145'])).
% 2.12/2.30  thf('147', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 2.12/2.30      inference('demod', [status(thm)], ['98', '99'])).
% 2.12/2.30  thf('148', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['105', '106'])).
% 2.12/2.30  thf('149', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['125', '126'])).
% 2.12/2.30  thf('150', plain,
% 2.12/2.30      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 2.12/2.30      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 2.12/2.30  thf('151', plain,
% 2.12/2.30      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 2.12/2.30      inference('simplify', [status(thm)], ['150'])).
% 2.12/2.30  thf('152', plain,
% 2.12/2.30      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['13', '14'])).
% 2.12/2.30  thf('153', plain,
% 2.12/2.30      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['28', '29'])).
% 2.12/2.30  thf('154', plain,
% 2.12/2.30      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30         (k1_zfmisc_1 @ 
% 2.12/2.30          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['43', '44'])).
% 2.12/2.30  thf('155', plain,
% 2.12/2.30      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.12/2.30         ((v1_xboole_0 @ X32)
% 2.12/2.30          | (v1_xboole_0 @ X33)
% 2.12/2.30          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 2.12/2.30          | ~ (v1_funct_1 @ X35)
% 2.12/2.30          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 2.12/2.30          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.12/2.30          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 2.12/2.30          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X33)
% 2.12/2.30              = (X35))
% 2.12/2.30          | ~ (m1_subset_1 @ X38 @ 
% 2.12/2.30               (k1_zfmisc_1 @ 
% 2.12/2.30                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 2.12/2.30          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 2.12/2.30          | ~ (v1_funct_1 @ X38)
% 2.12/2.30          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 2.12/2.30              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 2.12/2.30                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 2.12/2.30          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 2.12/2.30          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 2.12/2.30          | ~ (v1_funct_1 @ X36)
% 2.12/2.30          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 2.12/2.30          | (v1_xboole_0 @ X37)
% 2.12/2.30          | (v1_xboole_0 @ X34))),
% 2.12/2.30      inference('cnf', [status(esa)], [d1_tmap_1])).
% 2.12/2.30  thf('156', plain,
% 2.12/2.30      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.12/2.30         ((v1_xboole_0 @ X34)
% 2.12/2.30          | (v1_xboole_0 @ X37)
% 2.12/2.30          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 2.12/2.30          | ~ (v1_funct_1 @ X36)
% 2.12/2.30          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 2.12/2.30          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 2.12/2.30          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 2.12/2.30              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 2.12/2.30                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 2.12/2.30          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 2.12/2.30          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 2.12/2.30               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 2.12/2.30          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 2.12/2.30               (k1_zfmisc_1 @ 
% 2.12/2.30                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 2.12/2.30          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 2.12/2.30              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X33) = (
% 2.12/2.30              X35))
% 2.12/2.30          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.12/2.30          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 2.12/2.30          | ~ (v1_funct_1 @ X35)
% 2.12/2.30          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 2.12/2.30          | (v1_xboole_0 @ X33)
% 2.12/2.30          | (v1_xboole_0 @ X32))),
% 2.12/2.30      inference('simplify', [status(thm)], ['155'])).
% 2.12/2.30  thf('157', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.30        | ~ (v1_funct_1 @ sk_F)
% 2.12/2.30        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.12/2.30        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            = (sk_F))
% 2.12/2.30        | ~ (v1_funct_2 @ 
% 2.12/2.30             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 2.12/2.30            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 2.12/2.30        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 2.12/2.30        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 2.12/2.30        | ~ (v1_funct_1 @ sk_E)
% 2.12/2.30        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_A))),
% 2.12/2.30      inference('sup-', [status(thm)], ['154', '156'])).
% 2.12/2.30  thf('158', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('159', plain, ((v1_funct_1 @ sk_F)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('160', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('161', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('162', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.12/2.30      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.30  thf('163', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['81', '94'])).
% 2.12/2.30  thf('164', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 2.12/2.30      inference('demod', [status(thm)], ['98', '99'])).
% 2.12/2.30  thf('165', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['105', '106'])).
% 2.12/2.30  thf('166', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.12/2.30      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.30  thf('167', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 2.12/2.30      inference('demod', [status(thm)], ['81', '94'])).
% 2.12/2.30  thf('168', plain,
% 2.12/2.30      (![X0 : $i]:
% 2.12/2.30         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 2.12/2.30      inference('demod', [status(thm)], ['112', '113'])).
% 2.12/2.30  thf('169', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 2.12/2.30      inference('demod', [status(thm)], ['125', '126'])).
% 2.12/2.30  thf('170', plain,
% 2.12/2.30      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('171', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('172', plain, ((v1_funct_1 @ sk_E)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('173', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('174', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            = (sk_F))
% 2.12/2.30        | ~ (v1_funct_2 @ 
% 2.12/2.30             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ((k1_xboole_0) != (k1_xboole_0))
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_A))),
% 2.12/2.30      inference('demod', [status(thm)],
% 2.12/2.30                ['157', '158', '159', '160', '161', '162', '163', '164', 
% 2.12/2.30                 '165', '166', '167', '168', '169', '170', '171', '172', '173'])).
% 2.12/2.30  thf('175', plain,
% 2.12/2.30      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ~ (v1_funct_2 @ 
% 2.12/2.30             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            = (sk_F))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify', [status(thm)], ['174'])).
% 2.12/2.30  thf('176', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            = (sk_F))
% 2.12/2.30        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 2.12/2.30      inference('sup-', [status(thm)], ['153', '175'])).
% 2.12/2.30  thf('177', plain,
% 2.12/2.30      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            = (sk_F))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify', [status(thm)], ['176'])).
% 2.12/2.30  thf('178', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30            = (sk_F)))),
% 2.12/2.30      inference('sup-', [status(thm)], ['152', '177'])).
% 2.12/2.30  thf('179', plain,
% 2.12/2.30      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30          = (sk_F))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify', [status(thm)], ['178'])).
% 2.12/2.30  thf('180', plain,
% 2.12/2.30      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30          != (sk_F)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30                = (sk_F))))),
% 2.12/2.30      inference('split', [status(esa)], ['134'])).
% 2.12/2.30  thf('181', plain,
% 2.12/2.30      (((((sk_F) != (sk_F))
% 2.12/2.30         | (v1_xboole_0 @ sk_D)
% 2.12/2.30         | (v1_xboole_0 @ sk_C)
% 2.12/2.30         | (v1_xboole_0 @ sk_B)
% 2.12/2.30         | (v1_xboole_0 @ sk_A)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30                = (sk_F))))),
% 2.12/2.30      inference('sup-', [status(thm)], ['179', '180'])).
% 2.12/2.30  thf('182', plain,
% 2.12/2.30      ((((v1_xboole_0 @ sk_A)
% 2.12/2.30         | (v1_xboole_0 @ sk_B)
% 2.12/2.30         | (v1_xboole_0 @ sk_C)
% 2.12/2.30         | (v1_xboole_0 @ sk_D)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30                = (sk_F))))),
% 2.12/2.30      inference('simplify', [status(thm)], ['181'])).
% 2.12/2.30  thf('183', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('184', plain,
% 2.12/2.30      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30                = (sk_F))))),
% 2.12/2.30      inference('sup-', [status(thm)], ['182', '183'])).
% 2.12/2.30  thf('185', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('186', plain,
% 2.12/2.30      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30                = (sk_F))))),
% 2.12/2.30      inference('clc', [status(thm)], ['184', '185'])).
% 2.12/2.30  thf('187', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('188', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_B))
% 2.12/2.30         <= (~
% 2.12/2.30             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30                = (sk_F))))),
% 2.12/2.30      inference('clc', [status(thm)], ['186', '187'])).
% 2.12/2.30  thf('189', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('190', plain,
% 2.12/2.30      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30          = (sk_F)))),
% 2.12/2.30      inference('sup-', [status(thm)], ['188', '189'])).
% 2.12/2.30  thf('191', plain,
% 2.12/2.30      (~
% 2.12/2.30       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30          = (sk_E))) | 
% 2.12/2.30       ~
% 2.12/2.30       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.12/2.30          = (sk_F))) | 
% 2.12/2.30       ~
% 2.12/2.30       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 2.12/2.30          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.12/2.30             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 2.12/2.30      inference('split', [status(esa)], ['134'])).
% 2.12/2.30  thf('192', plain,
% 2.12/2.30      (~
% 2.12/2.30       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30          = (sk_E)))),
% 2.12/2.30      inference('sat_resolution*', [status(thm)], ['151', '190', '191'])).
% 2.12/2.30  thf('193', plain,
% 2.12/2.30      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 2.12/2.30         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 2.12/2.30         != (sk_E))),
% 2.12/2.30      inference('simpl_trail', [status(thm)], ['135', '192'])).
% 2.12/2.30  thf('194', plain,
% 2.12/2.30      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | ~ (v1_funct_2 @ 
% 2.12/2.30             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 2.12/2.30             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify_reflect-', [status(thm)], ['133', '193'])).
% 2.12/2.30  thf('195', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 2.12/2.30      inference('sup-', [status(thm)], ['30', '194'])).
% 2.12/2.30  thf('196', plain,
% 2.12/2.30      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify', [status(thm)], ['195'])).
% 2.12/2.30  thf('197', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_D)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_A))),
% 2.12/2.30      inference('sup-', [status(thm)], ['15', '196'])).
% 2.12/2.30  thf('198', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_A)
% 2.12/2.30        | (v1_xboole_0 @ sk_B)
% 2.12/2.30        | (v1_xboole_0 @ sk_C)
% 2.12/2.30        | (v1_xboole_0 @ sk_D))),
% 2.12/2.30      inference('simplify', [status(thm)], ['197'])).
% 2.12/2.30  thf('199', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('200', plain,
% 2.12/2.30      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 2.12/2.30      inference('sup-', [status(thm)], ['198', '199'])).
% 2.12/2.30  thf('201', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('202', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 2.12/2.30      inference('clc', [status(thm)], ['200', '201'])).
% 2.12/2.30  thf('203', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.12/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.30  thf('204', plain, ((v1_xboole_0 @ sk_B)),
% 2.12/2.30      inference('clc', [status(thm)], ['202', '203'])).
% 2.12/2.30  thf('205', plain, ($false), inference('demod', [status(thm)], ['0', '204'])).
% 2.12/2.30  
% 2.12/2.30  % SZS output end Refutation
% 2.12/2.30  
% 2.12/2.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
