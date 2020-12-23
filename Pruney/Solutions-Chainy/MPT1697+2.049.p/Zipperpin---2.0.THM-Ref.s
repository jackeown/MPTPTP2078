%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FOBADbfDGL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:00 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  283 (3332 expanded)
%              Number of leaves         :   42 ( 986 expanded)
%              Depth                    :   41
%              Number of atoms          : 3823 (119704 expanded)
%              Number of equality atoms :  135 (3977 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46 ) ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46 ) @ ( k4_subset_1 @ X45 @ X42 @ X44 ) @ X43 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X45 @ X42 @ X44 ) @ X43 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ( X40
       != ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 @ X40 @ X39 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k2_partfun1 @ X39 @ X34 @ X38 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) )
       != ( k2_partfun1 @ X35 @ X34 @ X37 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X34 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X34 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X34 ) ) )
      | ( ( k2_partfun1 @ X39 @ X34 @ X38 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) )
       != ( k2_partfun1 @ X35 @ X34 @ X37 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) @ X39 )
        = X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X31 @ X32 @ X30 @ X33 )
        = ( k7_relat_1 @ X30 @ X33 ) ) ) ),
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

thf('70',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
       => ( r1_subset_1 @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ( r1_subset_1 @ X18 @ X17 )
      | ~ ( r1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_subset_1])).

thf('72',plain,
    ( ( r1_subset_1 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_subset_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_subset_1 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('78',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['88','89'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('91',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('97',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['92','95','98'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['93','94'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['92','95','98'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('106',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = ( k3_xboole_0 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['93','94'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      = ( k3_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('112',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('115',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('116',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('119',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('120',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','118','121'])).

thf('123',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['110','111'])).

thf('128',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['110','111'])).

thf('129',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['119','120'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('133',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('135',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('136',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X31 @ X32 @ X30 @ X33 )
        = ( k7_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('142',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('144',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('154',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('157',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['151','154','157'])).

thf('159',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['152','153'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['141','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','133','134','135','140','163','164','165','166','167'])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('174',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['170'])).

thf('175',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('177',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['172','177'])).

thf('179',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('181',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('182',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('183',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['141','162'])).

thf('184',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182','183'])).

thf('185',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('187',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('188',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('189',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ( X40
       != ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 @ X40 @ X35 )
        = X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k2_partfun1 @ X39 @ X34 @ X38 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) )
       != ( k2_partfun1 @ X35 @ X34 @ X37 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X34 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('190',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X34 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X34 ) ) )
      | ( ( k2_partfun1 @ X39 @ X34 @ X38 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) )
       != ( k2_partfun1 @ X35 @ X34 @ X37 @ ( k9_subset_1 @ X36 @ X39 @ X35 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X36 @ X39 @ X35 ) @ X34 @ ( k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37 ) @ X35 )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
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
    inference('sup-',[status(thm)],['188','190'])).

thf('192',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('197',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('199',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('201',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('203',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['141','162'])).

thf('204',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
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
    inference(demod,[status(thm)],['191','192','193','194','195','196','197','198','199','200','201','202','203','204','205','206','207'])).

thf('209',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
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
    inference('sup-',[status(thm)],['187','209'])).

thf('211',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
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
    inference('sup-',[status(thm)],['186','211'])).

thf('213',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['170'])).

thf('215',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['170'])).

thf('226',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['185','224','225'])).

thf('227',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['171','226'])).

thf('228',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['169','227'])).

thf('229',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','228'])).

thf('230',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','230'])).

thf('232',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['234','235'])).

thf('237',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['236','237'])).

thf('239',plain,(
    $false ),
    inference(demod,[status(thm)],['0','238'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FOBADbfDGL
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.37/1.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.60  % Solved by: fo/fo7.sh
% 1.37/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.60  % done 1460 iterations in 1.157s
% 1.37/1.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.60  % SZS output start Refutation
% 1.37/1.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.60  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 1.37/1.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.37/1.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.37/1.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.37/1.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.60  thf(sk_F_type, type, sk_F: $i).
% 1.37/1.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.37/1.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.37/1.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.37/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.37/1.60  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 1.37/1.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.37/1.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.37/1.60  thf(sk_D_type, type, sk_D: $i).
% 1.37/1.60  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.60  thf(sk_E_type, type, sk_E: $i).
% 1.37/1.60  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.37/1.60  thf(t6_tmap_1, conjecture,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.37/1.60           ( ![C:$i]:
% 1.37/1.60             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.37/1.60                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.37/1.60               ( ![D:$i]:
% 1.37/1.60                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.37/1.60                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.37/1.60                   ( ( r1_subset_1 @ C @ D ) =>
% 1.37/1.60                     ( ![E:$i]:
% 1.37/1.60                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.37/1.60                           ( m1_subset_1 @
% 1.37/1.60                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.37/1.60                         ( ![F:$i]:
% 1.37/1.60                           ( ( ( v1_funct_1 @ F ) & 
% 1.37/1.60                               ( v1_funct_2 @ F @ D @ B ) & 
% 1.37/1.60                               ( m1_subset_1 @
% 1.37/1.60                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.37/1.60                             ( ( ( k2_partfun1 @
% 1.37/1.60                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.37/1.60                                 ( k2_partfun1 @
% 1.37/1.60                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.37/1.60                               ( ( k2_partfun1 @
% 1.37/1.60                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.37/1.60                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.37/1.60                                 ( E ) ) & 
% 1.37/1.60                               ( ( k2_partfun1 @
% 1.37/1.60                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.37/1.60                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.37/1.60                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.60    (~( ![A:$i]:
% 1.37/1.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.37/1.60          ( ![B:$i]:
% 1.37/1.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.37/1.60              ( ![C:$i]:
% 1.37/1.60                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.37/1.60                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.37/1.60                  ( ![D:$i]:
% 1.37/1.60                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.37/1.60                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.37/1.60                      ( ( r1_subset_1 @ C @ D ) =>
% 1.37/1.60                        ( ![E:$i]:
% 1.37/1.60                          ( ( ( v1_funct_1 @ E ) & 
% 1.37/1.60                              ( v1_funct_2 @ E @ C @ B ) & 
% 1.37/1.60                              ( m1_subset_1 @
% 1.37/1.60                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.37/1.60                            ( ![F:$i]:
% 1.37/1.60                              ( ( ( v1_funct_1 @ F ) & 
% 1.37/1.60                                  ( v1_funct_2 @ F @ D @ B ) & 
% 1.37/1.60                                  ( m1_subset_1 @
% 1.37/1.60                                    F @ 
% 1.37/1.60                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.37/1.60                                ( ( ( k2_partfun1 @
% 1.37/1.60                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.37/1.60                                    ( k2_partfun1 @
% 1.37/1.60                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.37/1.60                                  ( ( k2_partfun1 @
% 1.37/1.60                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.37/1.60                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.37/1.60                                    ( E ) ) & 
% 1.37/1.60                                  ( ( k2_partfun1 @
% 1.37/1.60                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.37/1.60                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.37/1.60                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.37/1.60    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 1.37/1.60  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('2', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('3', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(dt_k1_tmap_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.37/1.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.37/1.60         ( ~( v1_xboole_0 @ C ) ) & 
% 1.37/1.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 1.37/1.60         ( ~( v1_xboole_0 @ D ) ) & 
% 1.37/1.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 1.37/1.60         ( v1_funct_2 @ E @ C @ B ) & 
% 1.37/1.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.37/1.60         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.37/1.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.37/1.60       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.37/1.60         ( v1_funct_2 @
% 1.37/1.60           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.37/1.60           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.37/1.60         ( m1_subset_1 @
% 1.37/1.60           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.37/1.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 1.37/1.60  thf('4', plain,
% 1.37/1.60      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.37/1.60          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.37/1.60          | ~ (v1_funct_1 @ X41)
% 1.37/1.60          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.37/1.60          | (v1_xboole_0 @ X44)
% 1.37/1.60          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X45))
% 1.37/1.60          | (v1_xboole_0 @ X42)
% 1.37/1.60          | (v1_xboole_0 @ X43)
% 1.37/1.60          | (v1_xboole_0 @ X45)
% 1.37/1.60          | ~ (v1_funct_1 @ X46)
% 1.37/1.60          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 1.37/1.60          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 1.37/1.60          | (v1_funct_1 @ (k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46)))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.37/1.60  thf('5', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.37/1.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.37/1.60          | ~ (v1_funct_1 @ X0)
% 1.37/1.60          | (v1_xboole_0 @ X2)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 1.37/1.60          | (v1_xboole_0 @ X1)
% 1.37/1.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.37/1.60          | ~ (v1_funct_1 @ sk_E)
% 1.37/1.60          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['3', '4'])).
% 1.37/1.60  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('8', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.37/1.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.37/1.60          | ~ (v1_funct_1 @ X0)
% 1.37/1.60          | (v1_xboole_0 @ X2)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 1.37/1.60          | (v1_xboole_0 @ X1)
% 1.37/1.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.37/1.60      inference('demod', [status(thm)], ['5', '6', '7'])).
% 1.37/1.60  thf('9', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_D)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (v1_funct_1 @ sk_F)
% 1.37/1.60          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.37/1.60          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['2', '8'])).
% 1.37/1.60  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('12', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_D)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.37/1.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.37/1.60  thf('13', plain,
% 1.37/1.60      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['1', '12'])).
% 1.37/1.60  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('15', plain,
% 1.37/1.60      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['13', '14'])).
% 1.37/1.60  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('17', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('18', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('19', plain,
% 1.37/1.60      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.37/1.60          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.37/1.60          | ~ (v1_funct_1 @ X41)
% 1.37/1.60          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.37/1.60          | (v1_xboole_0 @ X44)
% 1.37/1.60          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X45))
% 1.37/1.60          | (v1_xboole_0 @ X42)
% 1.37/1.60          | (v1_xboole_0 @ X43)
% 1.37/1.60          | (v1_xboole_0 @ X45)
% 1.37/1.60          | ~ (v1_funct_1 @ X46)
% 1.37/1.60          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 1.37/1.60          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 1.37/1.60          | (v1_funct_2 @ (k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46) @ 
% 1.37/1.60             (k4_subset_1 @ X45 @ X42 @ X44) @ X43))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.37/1.60  thf('20', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.37/1.60           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 1.37/1.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.37/1.60          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.37/1.60          | ~ (v1_funct_1 @ X2)
% 1.37/1.60          | (v1_xboole_0 @ X1)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.60          | ~ (v1_funct_1 @ sk_E)
% 1.37/1.60          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.60  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('23', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.37/1.60           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 1.37/1.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.37/1.60          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.37/1.60          | ~ (v1_funct_1 @ X2)
% 1.37/1.60          | (v1_xboole_0 @ X1)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.37/1.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.37/1.60  thf('24', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_D)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (v1_funct_1 @ sk_F)
% 1.37/1.60          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.37/1.60          | (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['17', '23'])).
% 1.37/1.60  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('27', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_D)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 1.37/1.60      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.37/1.60  thf('28', plain,
% 1.37/1.60      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['16', '27'])).
% 1.37/1.60  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('30', plain,
% 1.37/1.60      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['28', '29'])).
% 1.37/1.60  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('32', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('33', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('34', plain,
% 1.37/1.60      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.37/1.60          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.37/1.60          | ~ (v1_funct_1 @ X41)
% 1.37/1.60          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 1.37/1.60          | (v1_xboole_0 @ X44)
% 1.37/1.60          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X45))
% 1.37/1.60          | (v1_xboole_0 @ X42)
% 1.37/1.60          | (v1_xboole_0 @ X43)
% 1.37/1.60          | (v1_xboole_0 @ X45)
% 1.37/1.60          | ~ (v1_funct_1 @ X46)
% 1.37/1.60          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 1.37/1.60          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 1.37/1.60          | (m1_subset_1 @ (k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46) @ 
% 1.37/1.60             (k1_zfmisc_1 @ 
% 1.37/1.60              (k2_zfmisc_1 @ (k4_subset_1 @ X45 @ X42 @ X44) @ X43))))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.37/1.60  thf('35', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.37/1.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 1.37/1.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.37/1.60          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.37/1.60          | ~ (v1_funct_1 @ X2)
% 1.37/1.60          | (v1_xboole_0 @ X1)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.37/1.60          | ~ (v1_funct_1 @ sk_E)
% 1.37/1.60          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 1.37/1.60      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.60  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('38', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.37/1.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 1.37/1.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.37/1.60          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.37/1.60          | ~ (v1_funct_1 @ X2)
% 1.37/1.60          | (v1_xboole_0 @ X1)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.37/1.60      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.37/1.60  thf('39', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_D)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | ~ (v1_funct_1 @ sk_F)
% 1.37/1.60          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.37/1.60          | (m1_subset_1 @ 
% 1.37/1.60             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k1_zfmisc_1 @ 
% 1.37/1.60              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['32', '38'])).
% 1.37/1.60  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('42', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_D)
% 1.37/1.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.37/1.60          | (v1_xboole_0 @ sk_C)
% 1.37/1.60          | (v1_xboole_0 @ sk_B)
% 1.37/1.60          | (v1_xboole_0 @ X0)
% 1.37/1.60          | (m1_subset_1 @ 
% 1.37/1.60             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k1_zfmisc_1 @ 
% 1.37/1.60              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 1.37/1.60      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.37/1.60  thf('43', plain,
% 1.37/1.60      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60         (k1_zfmisc_1 @ 
% 1.37/1.60          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['31', '42'])).
% 1.37/1.60  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('45', plain,
% 1.37/1.60      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60         (k1_zfmisc_1 @ 
% 1.37/1.60          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['43', '44'])).
% 1.37/1.60  thf(d1_tmap_1, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.37/1.60           ( ![C:$i]:
% 1.37/1.60             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.37/1.60                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.37/1.60               ( ![D:$i]:
% 1.37/1.60                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.37/1.60                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.37/1.60                   ( ![E:$i]:
% 1.37/1.60                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.37/1.60                         ( m1_subset_1 @
% 1.37/1.60                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.37/1.60                       ( ![F:$i]:
% 1.37/1.60                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.37/1.60                             ( m1_subset_1 @
% 1.37/1.60                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.37/1.60                           ( ( ( k2_partfun1 @
% 1.37/1.60                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.37/1.60                               ( k2_partfun1 @
% 1.37/1.60                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 1.37/1.60                             ( ![G:$i]:
% 1.37/1.60                               ( ( ( v1_funct_1 @ G ) & 
% 1.37/1.60                                   ( v1_funct_2 @
% 1.37/1.60                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.37/1.60                                   ( m1_subset_1 @
% 1.37/1.60                                     G @ 
% 1.37/1.60                                     ( k1_zfmisc_1 @
% 1.37/1.60                                       ( k2_zfmisc_1 @
% 1.37/1.60                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 1.37/1.60                                 ( ( ( G ) =
% 1.37/1.60                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.37/1.60                                   ( ( ( k2_partfun1 @
% 1.37/1.60                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.37/1.60                                         C ) =
% 1.37/1.60                                       ( E ) ) & 
% 1.37/1.60                                     ( ( k2_partfun1 @
% 1.37/1.60                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.37/1.60                                         D ) =
% 1.37/1.60                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.37/1.60  thf('46', plain,
% 1.37/1.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X34)
% 1.37/1.60          | (v1_xboole_0 @ X35)
% 1.37/1.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | ~ (v1_funct_1 @ X37)
% 1.37/1.60          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 1.37/1.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.37/1.60          | ((X40) != (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 1.37/1.60          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ X40 @ X39)
% 1.37/1.60              = (X38))
% 1.37/1.60          | ~ (m1_subset_1 @ X40 @ 
% 1.37/1.60               (k1_zfmisc_1 @ 
% 1.37/1.60                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 1.37/1.60          | ~ (v1_funct_2 @ X40 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 1.37/1.60          | ~ (v1_funct_1 @ X40)
% 1.37/1.60          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 1.37/1.60              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 1.37/1.60                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 1.37/1.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 1.37/1.60          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 1.37/1.60          | ~ (v1_funct_1 @ X38)
% 1.37/1.60          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | (v1_xboole_0 @ X39)
% 1.37/1.60          | (v1_xboole_0 @ X36))),
% 1.37/1.60      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.37/1.60  thf('47', plain,
% 1.37/1.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X36)
% 1.37/1.60          | (v1_xboole_0 @ X39)
% 1.37/1.60          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | ~ (v1_funct_1 @ X38)
% 1.37/1.60          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 1.37/1.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 1.37/1.60          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 1.37/1.60              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 1.37/1.60                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 1.37/1.60          | ~ (v1_funct_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 1.37/1.60          | ~ (v1_funct_2 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 1.37/1.60               (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 1.37/1.60          | ~ (m1_subset_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 1.37/1.60               (k1_zfmisc_1 @ 
% 1.37/1.60                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 1.37/1.60          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ 
% 1.37/1.60              (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ X39) = (
% 1.37/1.60              X38))
% 1.37/1.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.37/1.60          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 1.37/1.60          | ~ (v1_funct_1 @ X37)
% 1.37/1.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | (v1_xboole_0 @ X35)
% 1.37/1.60          | (v1_xboole_0 @ X34))),
% 1.37/1.60      inference('simplify', [status(thm)], ['46'])).
% 1.37/1.60  thf('48', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | ~ (v1_funct_1 @ sk_F)
% 1.37/1.60        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60            = (sk_E))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.37/1.60        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 1.37/1.60        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ sk_E)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['45', '47'])).
% 1.37/1.60  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('52', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(redefinition_k9_subset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.37/1.60       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.37/1.60  thf('54', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.37/1.60         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 1.37/1.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.37/1.60      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.37/1.60  thf('55', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.60  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(redefinition_r1_subset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.37/1.60       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 1.37/1.60  thf('57', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X15)
% 1.37/1.60          | (v1_xboole_0 @ X16)
% 1.37/1.60          | (r1_xboole_0 @ X15 @ X16)
% 1.37/1.60          | ~ (r1_subset_1 @ X15 @ X16))),
% 1.37/1.60      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 1.37/1.60  thf('58', plain,
% 1.37/1.60      (((r1_xboole_0 @ sk_C @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C))),
% 1.37/1.60      inference('sup-', [status(thm)], ['56', '57'])).
% 1.37/1.60  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.60      inference('clc', [status(thm)], ['58', '59'])).
% 1.37/1.60  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.37/1.60      inference('clc', [status(thm)], ['60', '61'])).
% 1.37/1.60  thf(d7_xboole_0, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.37/1.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.37/1.60  thf('63', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.37/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.60  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('65', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(redefinition_k2_partfun1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.60     ( ( ( v1_funct_1 @ C ) & 
% 1.37/1.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.60       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.37/1.60  thf('66', plain,
% 1.37/1.60      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.37/1.60          | ~ (v1_funct_1 @ X30)
% 1.37/1.60          | ((k2_partfun1 @ X31 @ X32 @ X30 @ X33) = (k7_relat_1 @ X30 @ X33)))),
% 1.37/1.60      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.37/1.60  thf('67', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 1.37/1.60          | ~ (v1_funct_1 @ sk_E))),
% 1.37/1.60      inference('sup-', [status(thm)], ['65', '66'])).
% 1.37/1.60  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('69', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['67', '68'])).
% 1.37/1.60  thf('70', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(symmetry_r1_subset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.37/1.60       ( ( r1_subset_1 @ A @ B ) => ( r1_subset_1 @ B @ A ) ) ))).
% 1.37/1.60  thf('71', plain,
% 1.37/1.60      (![X17 : $i, X18 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X17)
% 1.37/1.60          | (v1_xboole_0 @ X18)
% 1.37/1.60          | (r1_subset_1 @ X18 @ X17)
% 1.37/1.60          | ~ (r1_subset_1 @ X17 @ X18))),
% 1.37/1.60      inference('cnf', [status(esa)], [symmetry_r1_subset_1])).
% 1.37/1.60  thf('72', plain,
% 1.37/1.60      (((r1_subset_1 @ sk_D @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C))),
% 1.37/1.60      inference('sup-', [status(thm)], ['70', '71'])).
% 1.37/1.60  thf('73', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('74', plain, (((v1_xboole_0 @ sk_C) | (r1_subset_1 @ sk_D @ sk_C))),
% 1.37/1.60      inference('clc', [status(thm)], ['72', '73'])).
% 1.37/1.60  thf('75', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('76', plain, ((r1_subset_1 @ sk_D @ sk_C)),
% 1.37/1.60      inference('clc', [status(thm)], ['74', '75'])).
% 1.37/1.60  thf('77', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X15)
% 1.37/1.60          | (v1_xboole_0 @ X16)
% 1.37/1.60          | (r1_xboole_0 @ X15 @ X16)
% 1.37/1.60          | ~ (r1_subset_1 @ X15 @ X16))),
% 1.37/1.60      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 1.37/1.60  thf('78', plain,
% 1.37/1.60      (((r1_xboole_0 @ sk_D @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['76', '77'])).
% 1.37/1.60  thf('79', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('80', plain, (((v1_xboole_0 @ sk_D) | (r1_xboole_0 @ sk_D @ sk_C))),
% 1.37/1.60      inference('clc', [status(thm)], ['78', '79'])).
% 1.37/1.60  thf('81', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('82', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 1.37/1.60      inference('clc', [status(thm)], ['80', '81'])).
% 1.37/1.60  thf('83', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(cc5_funct_2, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.37/1.60       ( ![C:$i]:
% 1.37/1.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.60           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.37/1.60             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.37/1.60  thf('84', plain,
% 1.37/1.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.37/1.60          | (v1_partfun1 @ X25 @ X26)
% 1.37/1.60          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 1.37/1.60          | ~ (v1_funct_1 @ X25)
% 1.37/1.60          | (v1_xboole_0 @ X27))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.37/1.60  thf('85', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ sk_E)
% 1.37/1.60        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 1.37/1.60        | (v1_partfun1 @ sk_E @ sk_C))),
% 1.37/1.60      inference('sup-', [status(thm)], ['83', '84'])).
% 1.37/1.60  thf('86', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('87', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('88', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 1.37/1.60      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.37/1.60  thf('89', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('90', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 1.37/1.60      inference('clc', [status(thm)], ['88', '89'])).
% 1.37/1.60  thf(d4_partfun1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.37/1.60       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.37/1.60  thf('91', plain,
% 1.37/1.60      (![X28 : $i, X29 : $i]:
% 1.37/1.60         (~ (v1_partfun1 @ X29 @ X28)
% 1.37/1.60          | ((k1_relat_1 @ X29) = (X28))
% 1.37/1.60          | ~ (v4_relat_1 @ X29 @ X28)
% 1.37/1.60          | ~ (v1_relat_1 @ X29))),
% 1.37/1.60      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.37/1.60  thf('92', plain,
% 1.37/1.60      ((~ (v1_relat_1 @ sk_E)
% 1.37/1.60        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 1.37/1.60        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['90', '91'])).
% 1.37/1.60  thf('93', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(cc1_relset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.60       ( v1_relat_1 @ C ) ))).
% 1.37/1.60  thf('94', plain,
% 1.37/1.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.60         ((v1_relat_1 @ X19)
% 1.37/1.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.37/1.60  thf('95', plain, ((v1_relat_1 @ sk_E)),
% 1.37/1.60      inference('sup-', [status(thm)], ['93', '94'])).
% 1.37/1.60  thf('96', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(cc2_relset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.37/1.60  thf('97', plain,
% 1.37/1.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.60         ((v4_relat_1 @ X22 @ X23)
% 1.37/1.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.60  thf('98', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 1.37/1.60      inference('sup-', [status(thm)], ['96', '97'])).
% 1.37/1.60  thf('99', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.37/1.60      inference('demod', [status(thm)], ['92', '95', '98'])).
% 1.37/1.60  thf(t187_relat_1, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( v1_relat_1 @ A ) =>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 1.37/1.60           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.37/1.60  thf('100', plain,
% 1.37/1.60      (![X11 : $i, X12 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 1.37/1.60          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 1.37/1.60          | ~ (v1_relat_1 @ X12))),
% 1.37/1.60      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.37/1.60  thf('101', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.37/1.60          | ~ (v1_relat_1 @ sk_E)
% 1.37/1.60          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['99', '100'])).
% 1.37/1.60  thf('102', plain, ((v1_relat_1 @ sk_E)),
% 1.37/1.60      inference('sup-', [status(thm)], ['93', '94'])).
% 1.37/1.60  thf('103', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.37/1.60          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.37/1.60      inference('demod', [status(thm)], ['101', '102'])).
% 1.37/1.60  thf('104', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['82', '103'])).
% 1.37/1.60  thf('105', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.37/1.60      inference('demod', [status(thm)], ['92', '95', '98'])).
% 1.37/1.60  thf(t90_relat_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( v1_relat_1 @ B ) =>
% 1.37/1.60       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.37/1.60         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.37/1.60  thf('106', plain,
% 1.37/1.60      (![X13 : $i, X14 : $i]:
% 1.37/1.60         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 1.37/1.60            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 1.37/1.60          | ~ (v1_relat_1 @ X13))),
% 1.37/1.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.37/1.60  thf('107', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (k3_xboole_0 @ sk_C @ X0))
% 1.37/1.60          | ~ (v1_relat_1 @ sk_E))),
% 1.37/1.60      inference('sup+', [status(thm)], ['105', '106'])).
% 1.37/1.60  thf('108', plain, ((v1_relat_1 @ sk_E)),
% 1.37/1.60      inference('sup-', [status(thm)], ['93', '94'])).
% 1.37/1.60  thf('109', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (k3_xboole_0 @ sk_C @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['107', '108'])).
% 1.37/1.60  thf('110', plain,
% 1.37/1.60      (((k1_relat_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.60      inference('sup+', [status(thm)], ['104', '109'])).
% 1.37/1.60  thf('111', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('112', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['110', '111'])).
% 1.37/1.60  thf('113', plain,
% 1.37/1.60      (![X11 : $i, X12 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 1.37/1.60          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 1.37/1.60          | ~ (v1_relat_1 @ X12))),
% 1.37/1.60      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.37/1.60  thf('114', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.37/1.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.37/1.60          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['112', '113'])).
% 1.37/1.60  thf(t2_boole, axiom,
% 1.37/1.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.37/1.60  thf('115', plain,
% 1.37/1.60      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [t2_boole])).
% 1.37/1.60  thf('116', plain,
% 1.37/1.60      (![X0 : $i, X2 : $i]:
% 1.37/1.60         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.60  thf('117', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['115', '116'])).
% 1.37/1.60  thf('118', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.37/1.60      inference('simplify', [status(thm)], ['117'])).
% 1.37/1.60  thf(t4_subset_1, axiom,
% 1.37/1.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.37/1.60  thf('119', plain,
% 1.37/1.60      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.37/1.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.37/1.60  thf('120', plain,
% 1.37/1.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.60         ((v1_relat_1 @ X19)
% 1.37/1.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.37/1.60  thf('121', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.37/1.60      inference('sup-', [status(thm)], ['119', '120'])).
% 1.37/1.60  thf('122', plain,
% 1.37/1.60      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.37/1.60      inference('demod', [status(thm)], ['114', '118', '121'])).
% 1.37/1.60  thf('123', plain,
% 1.37/1.60      (![X13 : $i, X14 : $i]:
% 1.37/1.60         (((k1_relat_1 @ (k7_relat_1 @ X13 @ X14))
% 1.37/1.60            = (k3_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 1.37/1.60          | ~ (v1_relat_1 @ X13))),
% 1.37/1.60      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.37/1.60  thf('124', plain,
% 1.37/1.60      (![X0 : $i, X2 : $i]:
% 1.37/1.60         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.60  thf('125', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) != (k1_xboole_0))
% 1.37/1.60          | ~ (v1_relat_1 @ X1)
% 1.37/1.60          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['123', '124'])).
% 1.37/1.60  thf('126', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 1.37/1.60          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['122', '125'])).
% 1.37/1.60  thf('127', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['110', '111'])).
% 1.37/1.60  thf('128', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['110', '111'])).
% 1.37/1.60  thf('129', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.37/1.60      inference('sup-', [status(thm)], ['119', '120'])).
% 1.37/1.60  thf('130', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 1.37/1.60  thf('131', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.37/1.60      inference('simplify', [status(thm)], ['130'])).
% 1.37/1.60  thf('132', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.37/1.60          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.37/1.60      inference('demod', [status(thm)], ['101', '102'])).
% 1.37/1.60  thf('133', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['131', '132'])).
% 1.37/1.60  thf('134', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.60  thf('135', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('136', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('137', plain,
% 1.37/1.60      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.37/1.60          | ~ (v1_funct_1 @ X30)
% 1.37/1.60          | ((k2_partfun1 @ X31 @ X32 @ X30 @ X33) = (k7_relat_1 @ X30 @ X33)))),
% 1.37/1.60      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.37/1.60  thf('138', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 1.37/1.60          | ~ (v1_funct_1 @ sk_F))),
% 1.37/1.60      inference('sup-', [status(thm)], ['136', '137'])).
% 1.37/1.60  thf('139', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('140', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['138', '139'])).
% 1.37/1.60  thf('141', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.37/1.60      inference('simplify', [status(thm)], ['130'])).
% 1.37/1.60  thf('142', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('143', plain,
% 1.37/1.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.37/1.60          | (v1_partfun1 @ X25 @ X26)
% 1.37/1.60          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 1.37/1.60          | ~ (v1_funct_1 @ X25)
% 1.37/1.60          | (v1_xboole_0 @ X27))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.37/1.60  thf('144', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ sk_F)
% 1.37/1.60        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.37/1.60        | (v1_partfun1 @ sk_F @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['142', '143'])).
% 1.37/1.60  thf('145', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('146', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('147', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['144', '145', '146'])).
% 1.37/1.60  thf('148', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('149', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 1.37/1.60      inference('clc', [status(thm)], ['147', '148'])).
% 1.37/1.60  thf('150', plain,
% 1.37/1.60      (![X28 : $i, X29 : $i]:
% 1.37/1.60         (~ (v1_partfun1 @ X29 @ X28)
% 1.37/1.60          | ((k1_relat_1 @ X29) = (X28))
% 1.37/1.60          | ~ (v4_relat_1 @ X29 @ X28)
% 1.37/1.60          | ~ (v1_relat_1 @ X29))),
% 1.37/1.60      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.37/1.60  thf('151', plain,
% 1.37/1.60      ((~ (v1_relat_1 @ sk_F)
% 1.37/1.60        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 1.37/1.60        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['149', '150'])).
% 1.37/1.60  thf('152', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('153', plain,
% 1.37/1.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.60         ((v1_relat_1 @ X19)
% 1.37/1.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.37/1.60  thf('154', plain, ((v1_relat_1 @ sk_F)),
% 1.37/1.60      inference('sup-', [status(thm)], ['152', '153'])).
% 1.37/1.60  thf('155', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('156', plain,
% 1.37/1.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.60         ((v4_relat_1 @ X22 @ X23)
% 1.37/1.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.37/1.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.37/1.60  thf('157', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 1.37/1.60      inference('sup-', [status(thm)], ['155', '156'])).
% 1.37/1.60  thf('158', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['151', '154', '157'])).
% 1.37/1.60  thf('159', plain,
% 1.37/1.60      (![X11 : $i, X12 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 1.37/1.60          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 1.37/1.60          | ~ (v1_relat_1 @ X12))),
% 1.37/1.60      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.37/1.60  thf('160', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X0 @ sk_D)
% 1.37/1.60          | ~ (v1_relat_1 @ sk_F)
% 1.37/1.60          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['158', '159'])).
% 1.37/1.60  thf('161', plain, ((v1_relat_1 @ sk_F)),
% 1.37/1.60      inference('sup-', [status(thm)], ['152', '153'])).
% 1.37/1.60  thf('162', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (~ (r1_xboole_0 @ X0 @ sk_D)
% 1.37/1.60          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 1.37/1.60      inference('demod', [status(thm)], ['160', '161'])).
% 1.37/1.60  thf('163', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['141', '162'])).
% 1.37/1.60  thf('164', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('165', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('166', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('167', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('168', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60            = (sk_E))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)],
% 1.37/1.60                ['48', '49', '50', '51', '52', '55', '64', '69', '133', '134', 
% 1.37/1.60                 '135', '140', '163', '164', '165', '166', '167'])).
% 1.37/1.60  thf('169', plain,
% 1.37/1.60      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60            = (sk_E))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify', [status(thm)], ['168'])).
% 1.37/1.60  thf('170', plain,
% 1.37/1.60      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60            != (sk_E))
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            != (sk_F)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('171', plain,
% 1.37/1.60      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60          != (sk_E)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60                = (sk_E))))),
% 1.37/1.60      inference('split', [status(esa)], ['170'])).
% 1.37/1.60  thf('172', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['138', '139'])).
% 1.37/1.60  thf('173', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.60  thf('174', plain,
% 1.37/1.60      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.37/1.60      inference('split', [status(esa)], ['170'])).
% 1.37/1.60  thf('175', plain,
% 1.37/1.60      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['173', '174'])).
% 1.37/1.60  thf('176', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.60  thf('177', plain,
% 1.37/1.60      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 1.37/1.60          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.37/1.60      inference('demod', [status(thm)], ['175', '176'])).
% 1.37/1.60  thf('178', plain,
% 1.37/1.60      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 1.37/1.60          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['172', '177'])).
% 1.37/1.60  thf('179', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('180', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['67', '68'])).
% 1.37/1.60  thf('181', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['131', '132'])).
% 1.37/1.60  thf('182', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('183', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['141', '162'])).
% 1.37/1.60  thf('184', plain,
% 1.37/1.60      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.37/1.60      inference('demod', [status(thm)],
% 1.37/1.60                ['178', '179', '180', '181', '182', '183'])).
% 1.37/1.60  thf('185', plain,
% 1.37/1.60      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 1.37/1.60      inference('simplify', [status(thm)], ['184'])).
% 1.37/1.60  thf('186', plain,
% 1.37/1.60      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['13', '14'])).
% 1.37/1.60  thf('187', plain,
% 1.37/1.60      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['28', '29'])).
% 1.37/1.60  thf('188', plain,
% 1.37/1.60      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60         (k1_zfmisc_1 @ 
% 1.37/1.60          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('demod', [status(thm)], ['43', '44'])).
% 1.37/1.60  thf('189', plain,
% 1.37/1.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X34)
% 1.37/1.60          | (v1_xboole_0 @ X35)
% 1.37/1.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | ~ (v1_funct_1 @ X37)
% 1.37/1.60          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 1.37/1.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.37/1.60          | ((X40) != (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 1.37/1.60          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ X40 @ X35)
% 1.37/1.60              = (X37))
% 1.37/1.60          | ~ (m1_subset_1 @ X40 @ 
% 1.37/1.60               (k1_zfmisc_1 @ 
% 1.37/1.60                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 1.37/1.60          | ~ (v1_funct_2 @ X40 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 1.37/1.60          | ~ (v1_funct_1 @ X40)
% 1.37/1.60          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 1.37/1.60              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 1.37/1.60                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 1.37/1.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 1.37/1.60          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 1.37/1.60          | ~ (v1_funct_1 @ X38)
% 1.37/1.60          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | (v1_xboole_0 @ X39)
% 1.37/1.60          | (v1_xboole_0 @ X36))),
% 1.37/1.60      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.37/1.60  thf('190', plain,
% 1.37/1.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.37/1.60         ((v1_xboole_0 @ X36)
% 1.37/1.60          | (v1_xboole_0 @ X39)
% 1.37/1.60          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | ~ (v1_funct_1 @ X38)
% 1.37/1.60          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 1.37/1.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 1.37/1.60          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 1.37/1.60              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 1.37/1.60                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 1.37/1.60          | ~ (v1_funct_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 1.37/1.60          | ~ (v1_funct_2 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 1.37/1.60               (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 1.37/1.60          | ~ (m1_subset_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 1.37/1.60               (k1_zfmisc_1 @ 
% 1.37/1.60                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 1.37/1.60          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ 
% 1.37/1.60              (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ X35) = (
% 1.37/1.60              X37))
% 1.37/1.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.37/1.60          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 1.37/1.60          | ~ (v1_funct_1 @ X37)
% 1.37/1.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.37/1.60          | (v1_xboole_0 @ X35)
% 1.37/1.60          | (v1_xboole_0 @ X34))),
% 1.37/1.60      inference('simplify', [status(thm)], ['189'])).
% 1.37/1.60  thf('191', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | ~ (v1_funct_1 @ sk_F)
% 1.37/1.60        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            = (sk_F))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 1.37/1.60            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.37/1.60        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 1.37/1.60        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ sk_E)
% 1.37/1.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['188', '190'])).
% 1.37/1.60  thf('192', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('193', plain, ((v1_funct_1 @ sk_F)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('194', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('195', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('196', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.60  thf('197', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('198', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['67', '68'])).
% 1.37/1.60  thf('199', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['131', '132'])).
% 1.37/1.60  thf('200', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.37/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.37/1.60  thf('201', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.37/1.60  thf('202', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['138', '139'])).
% 1.37/1.60  thf('203', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['141', '162'])).
% 1.37/1.60  thf('204', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('205', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('206', plain, ((v1_funct_1 @ sk_E)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('207', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('208', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            = (sk_F))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('demod', [status(thm)],
% 1.37/1.60                ['191', '192', '193', '194', '195', '196', '197', '198', 
% 1.37/1.60                 '199', '200', '201', '202', '203', '204', '205', '206', '207'])).
% 1.37/1.60  thf('209', plain,
% 1.37/1.60      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            = (sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify', [status(thm)], ['208'])).
% 1.37/1.60  thf('210', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            = (sk_F))
% 1.37/1.60        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['187', '209'])).
% 1.37/1.60  thf('211', plain,
% 1.37/1.60      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            = (sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify', [status(thm)], ['210'])).
% 1.37/1.60  thf('212', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60            = (sk_F)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['186', '211'])).
% 1.37/1.60  thf('213', plain,
% 1.37/1.60      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60          = (sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify', [status(thm)], ['212'])).
% 1.37/1.60  thf('214', plain,
% 1.37/1.60      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60          != (sk_F)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60                = (sk_F))))),
% 1.37/1.60      inference('split', [status(esa)], ['170'])).
% 1.37/1.60  thf('215', plain,
% 1.37/1.60      (((((sk_F) != (sk_F))
% 1.37/1.60         | (v1_xboole_0 @ sk_D)
% 1.37/1.60         | (v1_xboole_0 @ sk_C)
% 1.37/1.60         | (v1_xboole_0 @ sk_B)
% 1.37/1.60         | (v1_xboole_0 @ sk_A)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60                = (sk_F))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['213', '214'])).
% 1.37/1.60  thf('216', plain,
% 1.37/1.60      ((((v1_xboole_0 @ sk_A)
% 1.37/1.60         | (v1_xboole_0 @ sk_B)
% 1.37/1.60         | (v1_xboole_0 @ sk_C)
% 1.37/1.60         | (v1_xboole_0 @ sk_D)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60                = (sk_F))))),
% 1.37/1.60      inference('simplify', [status(thm)], ['215'])).
% 1.37/1.60  thf('217', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('218', plain,
% 1.37/1.60      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60                = (sk_F))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['216', '217'])).
% 1.37/1.60  thf('219', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('220', plain,
% 1.37/1.60      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60                = (sk_F))))),
% 1.37/1.60      inference('clc', [status(thm)], ['218', '219'])).
% 1.37/1.60  thf('221', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('222', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_B))
% 1.37/1.60         <= (~
% 1.37/1.60             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60                = (sk_F))))),
% 1.37/1.60      inference('clc', [status(thm)], ['220', '221'])).
% 1.37/1.60  thf('223', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('224', plain,
% 1.37/1.60      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60          = (sk_F)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['222', '223'])).
% 1.37/1.60  thf('225', plain,
% 1.37/1.60      (~
% 1.37/1.60       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60          = (sk_E))) | 
% 1.37/1.60       ~
% 1.37/1.60       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.37/1.60          = (sk_F))) | 
% 1.37/1.60       ~
% 1.37/1.60       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.37/1.60          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.37/1.60             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 1.37/1.60      inference('split', [status(esa)], ['170'])).
% 1.37/1.60  thf('226', plain,
% 1.37/1.60      (~
% 1.37/1.60       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60          = (sk_E)))),
% 1.37/1.60      inference('sat_resolution*', [status(thm)], ['185', '224', '225'])).
% 1.37/1.60  thf('227', plain,
% 1.37/1.60      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 1.37/1.60         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.37/1.60         != (sk_E))),
% 1.37/1.60      inference('simpl_trail', [status(thm)], ['171', '226'])).
% 1.37/1.60  thf('228', plain,
% 1.37/1.60      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | ~ (v1_funct_2 @ 
% 1.37/1.60             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.37/1.60             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['169', '227'])).
% 1.37/1.60  thf('229', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['30', '228'])).
% 1.37/1.60  thf('230', plain,
% 1.37/1.60      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify', [status(thm)], ['229'])).
% 1.37/1.60  thf('231', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_D)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['15', '230'])).
% 1.37/1.60  thf('232', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_A)
% 1.37/1.60        | (v1_xboole_0 @ sk_B)
% 1.37/1.60        | (v1_xboole_0 @ sk_C)
% 1.37/1.60        | (v1_xboole_0 @ sk_D))),
% 1.37/1.60      inference('simplify', [status(thm)], ['231'])).
% 1.37/1.60  thf('233', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('234', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['232', '233'])).
% 1.37/1.60  thf('235', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('236', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 1.37/1.60      inference('clc', [status(thm)], ['234', '235'])).
% 1.37/1.60  thf('237', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('238', plain, ((v1_xboole_0 @ sk_B)),
% 1.37/1.60      inference('clc', [status(thm)], ['236', '237'])).
% 1.37/1.60  thf('239', plain, ($false), inference('demod', [status(thm)], ['0', '238'])).
% 1.37/1.60  
% 1.37/1.60  % SZS output end Refutation
% 1.37/1.60  
% 1.37/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
