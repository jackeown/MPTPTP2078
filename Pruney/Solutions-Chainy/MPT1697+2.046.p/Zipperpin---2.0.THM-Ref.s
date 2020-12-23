%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NMeWayK3Ah

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:00 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 904 expanded)
%              Number of leaves         :   42 ( 280 expanded)
%              Depth                    :   31
%              Number of atoms          : 3657 (35625 expanded)
%              Number of equality atoms :  117 (1141 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X47 @ X45 @ X44 @ X46 @ X43 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
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
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X47 @ X45 @ X44 @ X46 @ X43 @ X48 ) @ ( k4_subset_1 @ X47 @ X44 @ X46 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ),
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
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X47 @ X45 @ X44 @ X46 @ X43 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X47 @ X44 @ X46 ) @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ) ) ),
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
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ( X42
       != ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 @ X42 @ X41 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X41 @ X36 @ X40 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) )
       != ( k2_partfun1 @ X37 @ X36 @ X39 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X36 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X36 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X36 ) ) )
      | ( ( k2_partfun1 @ X41 @ X36 @ X40 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) )
       != ( k2_partfun1 @ X37 @ X36 @ X39 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) @ X41 )
        = X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_subset_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
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
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('66',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('75',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('76',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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

thf('82',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_partfun1 @ sk_E @ sk_C_1 ),
    inference(clc,[status(thm)],['86','87'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('95',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('96',plain,(
    v4_relat_1 @ sk_E @ sk_C_1 ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C_1 ),
    inference(demod,[status(thm)],['90','93','96'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('98',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k7_relat_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['91','92'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('105',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ( ( k2_partfun1 @ X33 @ X34 @ X32 @ X35 )
        = ( k7_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('126',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['120','123','126'])).

thf('128',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k7_relat_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['121','122'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','102','103','104','109','132','133','134','135','136'])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','138'])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('146',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('148',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('149',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('150',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('153',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','101'])).

thf('154',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','131'])).

thf('155',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('158',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('159',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('160',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ( X42
       != ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 @ X42 @ X37 )
        = X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 )
      | ~ ( v1_funct_1 @ X42 )
      | ( ( k2_partfun1 @ X41 @ X36 @ X40 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) )
       != ( k2_partfun1 @ X37 @ X36 @ X39 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X36 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('161',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X36 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X36 ) ) )
      | ( ( k2_partfun1 @ X41 @ X36 @ X40 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) )
       != ( k2_partfun1 @ X37 @ X36 @ X39 @ ( k9_subset_1 @ X38 @ X41 @ X37 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X38 @ X41 @ X37 ) @ X36 @ ( k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39 ) @ X37 )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('168',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('170',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','101'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('172',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('174',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','131'])).

thf('175',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','167','168','169','170','171','172','173','174','175','176','177','178'])).

thf('180',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['158','180'])).

thf('182',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['157','182'])).

thf('184',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['141'])).

thf('186',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['141'])).

thf('197',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['156','195','196'])).

thf('198',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['142','197'])).

thf('199',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['140','198'])).

thf('200',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','199'])).

thf('201',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    $false ),
    inference(demod,[status(thm)],['0','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NMeWayK3Ah
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 237 iterations in 0.203s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.66  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.66  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.66  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.66  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.66  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.66  thf(t6_tmap_1, conjecture,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.66           ( ![C:$i]:
% 0.44/0.66             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.66                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.66               ( ![D:$i]:
% 0.44/0.66                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.66                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.66                   ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.66                     ( ![E:$i]:
% 0.44/0.66                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.66                           ( m1_subset_1 @
% 0.44/0.66                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.66                         ( ![F:$i]:
% 0.44/0.66                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.66                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.66                               ( m1_subset_1 @
% 0.44/0.66                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.66                             ( ( ( k2_partfun1 @
% 0.44/0.66                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.66                                 ( k2_partfun1 @
% 0.44/0.66                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.66                               ( ( k2_partfun1 @
% 0.44/0.66                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.66                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.66                                 ( E ) ) & 
% 0.44/0.66                               ( ( k2_partfun1 @
% 0.44/0.66                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.66                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.66                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i]:
% 0.44/0.66        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.66          ( ![B:$i]:
% 0.44/0.66            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.66              ( ![C:$i]:
% 0.44/0.66                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.66                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.66                  ( ![D:$i]:
% 0.44/0.66                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.66                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.66                      ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.66                        ( ![E:$i]:
% 0.44/0.66                          ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.66                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.66                              ( m1_subset_1 @
% 0.44/0.66                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.66                            ( ![F:$i]:
% 0.44/0.66                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.66                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.66                                  ( m1_subset_1 @
% 0.44/0.66                                    F @ 
% 0.44/0.66                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.66                                ( ( ( k2_partfun1 @
% 0.44/0.66                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.66                                    ( k2_partfun1 @
% 0.44/0.66                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.66                                  ( ( k2_partfun1 @
% 0.44/0.66                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.66                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.66                                    ( E ) ) & 
% 0.44/0.66                                  ( ( k2_partfun1 @
% 0.44/0.66                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.66                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.66                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.44/0.66  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(dt_k1_tmap_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.66         ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.66         ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.44/0.66         ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.44/0.66         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.66       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.66         ( v1_funct_2 @
% 0.44/0.66           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.66           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.66         ( m1_subset_1 @
% 0.44/0.66           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.44/0.66          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.44/0.66          | ~ (v1_funct_1 @ X43)
% 0.44/0.66          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.44/0.66          | (v1_xboole_0 @ X46)
% 0.44/0.66          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X47))
% 0.44/0.66          | (v1_xboole_0 @ X44)
% 0.44/0.66          | (v1_xboole_0 @ X45)
% 0.44/0.66          | (v1_xboole_0 @ X47)
% 0.44/0.66          | ~ (v1_funct_1 @ X48)
% 0.44/0.66          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 0.44/0.66          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.44/0.66          | (v1_funct_1 @ (k1_tmap_1 @ X47 @ X45 @ X44 @ X46 @ X43 @ X48)))),
% 0.44/0.66      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.44/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.66          | ~ (v1_funct_1 @ X0)
% 0.44/0.66          | (v1_xboole_0 @ X2)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.66          | (v1_xboole_0 @ X1)
% 0.44/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.66          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.66          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.66  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.44/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.66          | ~ (v1_funct_1 @ X0)
% 0.44/0.66          | (v1_xboole_0 @ X2)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.66          | (v1_xboole_0 @ X1)
% 0.44/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.66      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_D)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.66          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.66          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.66  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_D)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.66      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['1', '12'])).
% 0.44/0.66  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.44/0.66          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.44/0.66          | ~ (v1_funct_1 @ X43)
% 0.44/0.66          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.44/0.66          | (v1_xboole_0 @ X46)
% 0.44/0.66          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X47))
% 0.44/0.66          | (v1_xboole_0 @ X44)
% 0.44/0.66          | (v1_xboole_0 @ X45)
% 0.44/0.66          | (v1_xboole_0 @ X47)
% 0.44/0.66          | ~ (v1_funct_1 @ X48)
% 0.44/0.66          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 0.44/0.66          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.44/0.66          | (v1_funct_2 @ (k1_tmap_1 @ X47 @ X45 @ X44 @ X46 @ X43 @ X48) @ 
% 0.44/0.66             (k4_subset_1 @ X47 @ X44 @ X46) @ X45))),
% 0.44/0.66      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.66           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.44/0.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.66          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.66          | ~ (v1_funct_1 @ X2)
% 0.44/0.66          | (v1_xboole_0 @ X1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.66          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.66  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('23', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.66           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.44/0.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.66          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.66          | ~ (v1_funct_1 @ X2)
% 0.44/0.66          | (v1_xboole_0 @ X1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.66      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.66  thf('24', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_D)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.66          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.66          | (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['17', '23'])).
% 0.44/0.66  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_D)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 0.44/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.66  thf('28', plain,
% 0.44/0.66      (((v1_funct_2 @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['16', '27'])).
% 0.44/0.66  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (((v1_funct_2 @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.66  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('32', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('33', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('34', plain,
% 0.44/0.66      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.44/0.66          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.44/0.66          | ~ (v1_funct_1 @ X43)
% 0.44/0.66          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 0.44/0.66          | (v1_xboole_0 @ X46)
% 0.44/0.66          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X47))
% 0.44/0.66          | (v1_xboole_0 @ X44)
% 0.44/0.66          | (v1_xboole_0 @ X45)
% 0.44/0.66          | (v1_xboole_0 @ X47)
% 0.44/0.66          | ~ (v1_funct_1 @ X48)
% 0.44/0.66          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 0.44/0.66          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.44/0.66          | (m1_subset_1 @ (k1_tmap_1 @ X47 @ X45 @ X44 @ X46 @ X43 @ X48) @ 
% 0.44/0.66             (k1_zfmisc_1 @ 
% 0.44/0.66              (k2_zfmisc_1 @ (k4_subset_1 @ X47 @ X44 @ X46) @ X45))))),
% 0.44/0.66      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.66  thf('35', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.66           (k1_zfmisc_1 @ 
% 0.44/0.66            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.44/0.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.66          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.66          | ~ (v1_funct_1 @ X2)
% 0.44/0.66          | (v1_xboole_0 @ X1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.66          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.44/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.66  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('38', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.66           (k1_zfmisc_1 @ 
% 0.44/0.66            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.44/0.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.66          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.66          | ~ (v1_funct_1 @ X2)
% 0.44/0.66          | (v1_xboole_0 @ X1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.44/0.66  thf('39', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_D)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.66          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.66          | (m1_subset_1 @ 
% 0.44/0.66             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k1_zfmisc_1 @ 
% 0.44/0.66              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['32', '38'])).
% 0.44/0.66  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('42', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_D)
% 0.44/0.66          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.66          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66          | (v1_xboole_0 @ sk_B)
% 0.44/0.66          | (v1_xboole_0 @ X0)
% 0.44/0.66          | (m1_subset_1 @ 
% 0.44/0.66             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k1_zfmisc_1 @ 
% 0.44/0.66              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 0.44/0.66      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.66  thf('43', plain,
% 0.44/0.66      (((m1_subset_1 @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66         (k1_zfmisc_1 @ 
% 0.44/0.66          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['31', '42'])).
% 0.44/0.66  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('45', plain,
% 0.44/0.66      (((m1_subset_1 @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66         (k1_zfmisc_1 @ 
% 0.44/0.66          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.66  thf(d1_tmap_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.66           ( ![C:$i]:
% 0.44/0.66             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.66                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.66               ( ![D:$i]:
% 0.44/0.66                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.66                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.66                   ( ![E:$i]:
% 0.44/0.66                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.66                         ( m1_subset_1 @
% 0.44/0.66                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.66                       ( ![F:$i]:
% 0.44/0.66                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.66                             ( m1_subset_1 @
% 0.44/0.66                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.66                           ( ( ( k2_partfun1 @
% 0.44/0.66                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.66                               ( k2_partfun1 @
% 0.44/0.66                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.44/0.66                             ( ![G:$i]:
% 0.44/0.66                               ( ( ( v1_funct_1 @ G ) & 
% 0.44/0.66                                   ( v1_funct_2 @
% 0.44/0.66                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.66                                   ( m1_subset_1 @
% 0.44/0.66                                     G @ 
% 0.44/0.66                                     ( k1_zfmisc_1 @
% 0.44/0.66                                       ( k2_zfmisc_1 @
% 0.44/0.66                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.44/0.66                                 ( ( ( G ) =
% 0.44/0.66                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.66                                   ( ( ( k2_partfun1 @
% 0.44/0.66                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.66                                         C ) =
% 0.44/0.66                                       ( E ) ) & 
% 0.44/0.66                                     ( ( k2_partfun1 @
% 0.44/0.66                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.66                                         D ) =
% 0.44/0.66                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.66  thf('46', plain,
% 0.44/0.66      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.66         ((v1_xboole_0 @ X36)
% 0.44/0.66          | (v1_xboole_0 @ X37)
% 0.44/0.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | ~ (v1_funct_1 @ X39)
% 0.44/0.66          | ~ (v1_funct_2 @ X39 @ X37 @ X36)
% 0.44/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.44/0.66          | ((X42) != (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39))
% 0.44/0.66          | ((k2_partfun1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36 @ X42 @ X41)
% 0.44/0.66              = (X40))
% 0.44/0.66          | ~ (m1_subset_1 @ X42 @ 
% 0.44/0.66               (k1_zfmisc_1 @ 
% 0.44/0.66                (k2_zfmisc_1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36)))
% 0.44/0.66          | ~ (v1_funct_2 @ X42 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36)
% 0.44/0.66          | ~ (v1_funct_1 @ X42)
% 0.44/0.66          | ((k2_partfun1 @ X41 @ X36 @ X40 @ (k9_subset_1 @ X38 @ X41 @ X37))
% 0.44/0.66              != (k2_partfun1 @ X37 @ X36 @ X39 @ 
% 0.44/0.66                  (k9_subset_1 @ X38 @ X41 @ X37)))
% 0.44/0.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X36)))
% 0.44/0.66          | ~ (v1_funct_2 @ X40 @ X41 @ X36)
% 0.44/0.66          | ~ (v1_funct_1 @ X40)
% 0.44/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | (v1_xboole_0 @ X41)
% 0.44/0.66          | (v1_xboole_0 @ X38))),
% 0.44/0.66      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.66  thf('47', plain,
% 0.44/0.66      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.44/0.66         ((v1_xboole_0 @ X38)
% 0.44/0.66          | (v1_xboole_0 @ X41)
% 0.44/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | ~ (v1_funct_1 @ X40)
% 0.44/0.66          | ~ (v1_funct_2 @ X40 @ X41 @ X36)
% 0.44/0.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X36)))
% 0.44/0.66          | ((k2_partfun1 @ X41 @ X36 @ X40 @ (k9_subset_1 @ X38 @ X41 @ X37))
% 0.44/0.66              != (k2_partfun1 @ X37 @ X36 @ X39 @ 
% 0.44/0.66                  (k9_subset_1 @ X38 @ X41 @ X37)))
% 0.44/0.66          | ~ (v1_funct_1 @ (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39))
% 0.44/0.66          | ~ (v1_funct_2 @ (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39) @ 
% 0.44/0.66               (k4_subset_1 @ X38 @ X41 @ X37) @ X36)
% 0.44/0.66          | ~ (m1_subset_1 @ (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39) @ 
% 0.44/0.66               (k1_zfmisc_1 @ 
% 0.44/0.66                (k2_zfmisc_1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36)))
% 0.44/0.66          | ((k2_partfun1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36 @ 
% 0.44/0.66              (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39) @ X41) = (
% 0.44/0.66              X40))
% 0.44/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.44/0.66          | ~ (v1_funct_2 @ X39 @ X37 @ X36)
% 0.44/0.66          | ~ (v1_funct_1 @ X39)
% 0.44/0.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | (v1_xboole_0 @ X37)
% 0.44/0.66          | (v1_xboole_0 @ X36))),
% 0.44/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.66  thf('48', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.66        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66            = (sk_E))
% 0.44/0.66        | ~ (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.44/0.66        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.44/0.66        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['45', '47'])).
% 0.44/0.66  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('52', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.66       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.66  thf('54', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.66         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.44/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.66  thf('55', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.66       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.66  thf('57', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i]:
% 0.44/0.66         ((v1_xboole_0 @ X19)
% 0.44/0.66          | (v1_xboole_0 @ X20)
% 0.44/0.66          | (r1_xboole_0 @ X19 @ X20)
% 0.44/0.66          | ~ (r1_subset_1 @ X19 @ X20))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.66  thf('58', plain,
% 0.44/0.66      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.66  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.44/0.66      inference('clc', [status(thm)], ['58', '59'])).
% 0.44/0.66  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.44/0.66      inference('clc', [status(thm)], ['60', '61'])).
% 0.44/0.66  thf(d7_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.66  thf('63', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.66  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('65', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.66       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.66  thf('66', plain,
% 0.44/0.66      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.44/0.66          | ~ (v1_funct_1 @ X32)
% 0.44/0.66          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.66  thf('67', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.66          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.66  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('69', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.66  thf(t2_boole, axiom,
% 0.44/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.66  thf('70', plain,
% 0.44/0.66      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.66  thf('71', plain,
% 0.44/0.66      (![X0 : $i, X2 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.66  thf('72', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.66  thf('73', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.44/0.66      inference('simplify', [status(thm)], ['72'])).
% 0.44/0.66  thf(t3_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.44/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.66            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.44/0.66  thf('74', plain,
% 0.44/0.66      (![X3 : $i, X4 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.66  thf('75', plain,
% 0.44/0.66      (![X3 : $i, X4 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.66  thf('76', plain,
% 0.44/0.66      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X5 @ X3)
% 0.44/0.66          | ~ (r2_hidden @ X5 @ X6)
% 0.44/0.66          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.44/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.66  thf('77', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.44/0.66          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.44/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.44/0.66  thf('78', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((r1_xboole_0 @ X0 @ X1)
% 0.44/0.66          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.44/0.66          | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['74', '77'])).
% 0.44/0.66  thf('79', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('simplify', [status(thm)], ['78'])).
% 0.44/0.66  thf('80', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.66      inference('sup-', [status(thm)], ['73', '79'])).
% 0.44/0.66  thf('81', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(cc5_funct_2, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.66       ( ![C:$i]:
% 0.44/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.66             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.66  thf('82', plain,
% 0.44/0.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.66          | (v1_partfun1 @ X27 @ X28)
% 0.44/0.66          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.44/0.66          | ~ (v1_funct_1 @ X27)
% 0.44/0.66          | (v1_xboole_0 @ X29))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.66  thf('83', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.66        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.44/0.66        | (v1_partfun1 @ sk_E @ sk_C_1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['81', '82'])).
% 0.44/0.66  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('85', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('86', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.44/0.66  thf('87', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('88', plain, ((v1_partfun1 @ sk_E @ sk_C_1)),
% 0.44/0.66      inference('clc', [status(thm)], ['86', '87'])).
% 0.44/0.66  thf(d4_partfun1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.66  thf('89', plain,
% 0.44/0.66      (![X30 : $i, X31 : $i]:
% 0.44/0.66         (~ (v1_partfun1 @ X31 @ X30)
% 0.44/0.66          | ((k1_relat_1 @ X31) = (X30))
% 0.44/0.66          | ~ (v4_relat_1 @ X31 @ X30)
% 0.44/0.66          | ~ (v1_relat_1 @ X31))),
% 0.44/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.66  thf('90', plain,
% 0.44/0.66      ((~ (v1_relat_1 @ sk_E)
% 0.44/0.66        | ~ (v4_relat_1 @ sk_E @ sk_C_1)
% 0.44/0.66        | ((k1_relat_1 @ sk_E) = (sk_C_1)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['88', '89'])).
% 0.44/0.66  thf('91', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(cc1_relset_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66       ( v1_relat_1 @ C ) ))).
% 0.44/0.66  thf('92', plain,
% 0.44/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.66         ((v1_relat_1 @ X21)
% 0.44/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.66  thf('93', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.66  thf('94', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(cc2_relset_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.66  thf('95', plain,
% 0.44/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.66         ((v4_relat_1 @ X24 @ X25)
% 0.44/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.66  thf('96', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 0.44/0.66      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.66  thf('97', plain, (((k1_relat_1 @ sk_E) = (sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['90', '93', '96'])).
% 0.44/0.66  thf(t187_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.66           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.66  thf('98', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X17 @ (k1_relat_1 @ X18))
% 0.44/0.66          | ((k7_relat_1 @ X18 @ X17) = (k1_xboole_0))
% 0.44/0.66          | ~ (v1_relat_1 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.66  thf('99', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 0.44/0.66          | ~ (v1_relat_1 @ sk_E)
% 0.44/0.66          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['97', '98'])).
% 0.44/0.66  thf('100', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.66  thf('101', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 0.44/0.66          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['99', '100'])).
% 0.44/0.66  thf('102', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['80', '101'])).
% 0.44/0.66  thf('103', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('104', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('105', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('106', plain,
% 0.44/0.66      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.44/0.66          | ~ (v1_funct_1 @ X32)
% 0.44/0.66          | ((k2_partfun1 @ X33 @ X34 @ X32 @ X35) = (k7_relat_1 @ X32 @ X35)))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.66  thf('107', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.66          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.66      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.66  thf('108', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('109', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['107', '108'])).
% 0.44/0.66  thf('110', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.66      inference('sup-', [status(thm)], ['73', '79'])).
% 0.44/0.66  thf('111', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('112', plain,
% 0.44/0.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.66          | (v1_partfun1 @ X27 @ X28)
% 0.44/0.66          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.44/0.66          | ~ (v1_funct_1 @ X27)
% 0.44/0.66          | (v1_xboole_0 @ X29))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.66  thf('113', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.66        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.66        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['111', '112'])).
% 0.44/0.66  thf('114', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('115', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('116', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.44/0.66  thf('117', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('118', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.44/0.66      inference('clc', [status(thm)], ['116', '117'])).
% 0.44/0.66  thf('119', plain,
% 0.44/0.66      (![X30 : $i, X31 : $i]:
% 0.44/0.66         (~ (v1_partfun1 @ X31 @ X30)
% 0.44/0.66          | ((k1_relat_1 @ X31) = (X30))
% 0.44/0.66          | ~ (v4_relat_1 @ X31 @ X30)
% 0.44/0.66          | ~ (v1_relat_1 @ X31))),
% 0.44/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.66  thf('120', plain,
% 0.44/0.66      ((~ (v1_relat_1 @ sk_F)
% 0.44/0.66        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.44/0.66        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['118', '119'])).
% 0.44/0.66  thf('121', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('122', plain,
% 0.44/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.66         ((v1_relat_1 @ X21)
% 0.44/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.66  thf('123', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.66      inference('sup-', [status(thm)], ['121', '122'])).
% 0.44/0.66  thf('124', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('125', plain,
% 0.44/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.66         ((v4_relat_1 @ X24 @ X25)
% 0.44/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.66  thf('126', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.44/0.66      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.66  thf('127', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['120', '123', '126'])).
% 0.44/0.66  thf('128', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X17 @ (k1_relat_1 @ X18))
% 0.44/0.66          | ((k7_relat_1 @ X18 @ X17) = (k1_xboole_0))
% 0.44/0.66          | ~ (v1_relat_1 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.66  thf('129', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.66          | ~ (v1_relat_1 @ sk_F)
% 0.44/0.66          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['127', '128'])).
% 0.44/0.66  thf('130', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.66      inference('sup-', [status(thm)], ['121', '122'])).
% 0.44/0.66  thf('131', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.66          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['129', '130'])).
% 0.44/0.66  thf('132', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['110', '131'])).
% 0.44/0.66  thf('133', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('134', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('135', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('136', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('137', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66            = (sk_E))
% 0.44/0.66        | ~ (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)],
% 0.44/0.66                ['48', '49', '50', '51', '52', '55', '64', '69', '102', '103', 
% 0.44/0.66                 '104', '109', '132', '133', '134', '135', '136'])).
% 0.44/0.66  thf('138', plain,
% 0.44/0.66      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ~ (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66            = (sk_E))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify', [status(thm)], ['137'])).
% 0.44/0.66  thf('139', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66            = (sk_E))
% 0.44/0.66        | ~ (v1_funct_1 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['30', '138'])).
% 0.44/0.66  thf('140', plain,
% 0.44/0.66      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66            = (sk_E))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.44/0.66  thf('141', plain,
% 0.44/0.66      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66            != (sk_E))
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            != (sk_F)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('142', plain,
% 0.44/0.66      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66          != (sk_E)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66                sk_C_1) = (sk_E))))),
% 0.44/0.66      inference('split', [status(esa)], ['141'])).
% 0.44/0.66  thf('143', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['107', '108'])).
% 0.44/0.66  thf('144', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('145', plain,
% 0.44/0.66      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.66      inference('split', [status(esa)], ['141'])).
% 0.44/0.66  thf('146', plain,
% 0.44/0.66      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['144', '145'])).
% 0.44/0.66  thf('147', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('148', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('149', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('150', plain,
% 0.44/0.66      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.66          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.66      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.44/0.66  thf('151', plain,
% 0.44/0.66      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.66          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['143', '150'])).
% 0.44/0.66  thf('152', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.66  thf('153', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['80', '101'])).
% 0.44/0.66  thf('154', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['110', '131'])).
% 0.44/0.66  thf('155', plain,
% 0.44/0.66      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.66      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.44/0.66  thf('156', plain,
% 0.44/0.66      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.44/0.66      inference('simplify', [status(thm)], ['155'])).
% 0.44/0.66  thf('157', plain,
% 0.44/0.66      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf('158', plain,
% 0.44/0.66      (((v1_funct_2 @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.66  thf('159', plain,
% 0.44/0.66      (((m1_subset_1 @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66         (k1_zfmisc_1 @ 
% 0.44/0.66          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.66  thf('160', plain,
% 0.44/0.66      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.66         ((v1_xboole_0 @ X36)
% 0.44/0.66          | (v1_xboole_0 @ X37)
% 0.44/0.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | ~ (v1_funct_1 @ X39)
% 0.44/0.66          | ~ (v1_funct_2 @ X39 @ X37 @ X36)
% 0.44/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.44/0.66          | ((X42) != (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39))
% 0.44/0.66          | ((k2_partfun1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36 @ X42 @ X37)
% 0.44/0.66              = (X39))
% 0.44/0.66          | ~ (m1_subset_1 @ X42 @ 
% 0.44/0.66               (k1_zfmisc_1 @ 
% 0.44/0.66                (k2_zfmisc_1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36)))
% 0.44/0.66          | ~ (v1_funct_2 @ X42 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36)
% 0.44/0.66          | ~ (v1_funct_1 @ X42)
% 0.44/0.66          | ((k2_partfun1 @ X41 @ X36 @ X40 @ (k9_subset_1 @ X38 @ X41 @ X37))
% 0.44/0.66              != (k2_partfun1 @ X37 @ X36 @ X39 @ 
% 0.44/0.66                  (k9_subset_1 @ X38 @ X41 @ X37)))
% 0.44/0.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X36)))
% 0.44/0.66          | ~ (v1_funct_2 @ X40 @ X41 @ X36)
% 0.44/0.66          | ~ (v1_funct_1 @ X40)
% 0.44/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | (v1_xboole_0 @ X41)
% 0.44/0.66          | (v1_xboole_0 @ X38))),
% 0.44/0.66      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.66  thf('161', plain,
% 0.44/0.66      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.44/0.66         ((v1_xboole_0 @ X38)
% 0.44/0.66          | (v1_xboole_0 @ X41)
% 0.44/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | ~ (v1_funct_1 @ X40)
% 0.44/0.66          | ~ (v1_funct_2 @ X40 @ X41 @ X36)
% 0.44/0.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X36)))
% 0.44/0.66          | ((k2_partfun1 @ X41 @ X36 @ X40 @ (k9_subset_1 @ X38 @ X41 @ X37))
% 0.44/0.66              != (k2_partfun1 @ X37 @ X36 @ X39 @ 
% 0.44/0.66                  (k9_subset_1 @ X38 @ X41 @ X37)))
% 0.44/0.66          | ~ (v1_funct_1 @ (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39))
% 0.44/0.66          | ~ (v1_funct_2 @ (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39) @ 
% 0.44/0.66               (k4_subset_1 @ X38 @ X41 @ X37) @ X36)
% 0.44/0.66          | ~ (m1_subset_1 @ (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39) @ 
% 0.44/0.66               (k1_zfmisc_1 @ 
% 0.44/0.66                (k2_zfmisc_1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36)))
% 0.44/0.66          | ((k2_partfun1 @ (k4_subset_1 @ X38 @ X41 @ X37) @ X36 @ 
% 0.44/0.66              (k1_tmap_1 @ X38 @ X36 @ X41 @ X37 @ X40 @ X39) @ X37) = (
% 0.44/0.66              X39))
% 0.44/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.44/0.66          | ~ (v1_funct_2 @ X39 @ X37 @ X36)
% 0.44/0.66          | ~ (v1_funct_1 @ X39)
% 0.44/0.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 0.44/0.66          | (v1_xboole_0 @ X37)
% 0.44/0.66          | (v1_xboole_0 @ X36))),
% 0.44/0.66      inference('simplify', [status(thm)], ['160'])).
% 0.44/0.66  thf('162', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.66        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            = (sk_F))
% 0.44/0.66        | ~ (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.44/0.66        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.44/0.66        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.66        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['159', '161'])).
% 0.44/0.66  thf('163', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('164', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('165', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('166', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('167', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('168', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('169', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.66  thf('170', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['80', '101'])).
% 0.44/0.66  thf('171', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('172', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.66  thf('173', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.66      inference('demod', [status(thm)], ['107', '108'])).
% 0.44/0.66  thf('174', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['110', '131'])).
% 0.44/0.66  thf('175', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('176', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('177', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('178', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('179', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            = (sk_F))
% 0.44/0.66        | ~ (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | ~ (v1_funct_1 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_A))),
% 0.44/0.66      inference('demod', [status(thm)],
% 0.44/0.66                ['162', '163', '164', '165', '166', '167', '168', '169', 
% 0.44/0.66                 '170', '171', '172', '173', '174', '175', '176', '177', '178'])).
% 0.44/0.66  thf('180', plain,
% 0.44/0.66      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ~ (v1_funct_2 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.66             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            = (sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify', [status(thm)], ['179'])).
% 0.44/0.66  thf('181', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            = (sk_F))
% 0.44/0.66        | ~ (v1_funct_1 @ 
% 0.44/0.66             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['158', '180'])).
% 0.44/0.66  thf('182', plain,
% 0.44/0.66      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            = (sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify', [status(thm)], ['181'])).
% 0.44/0.66  thf('183', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66            = (sk_F)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['157', '182'])).
% 0.44/0.66  thf('184', plain,
% 0.44/0.66      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66          = (sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify', [status(thm)], ['183'])).
% 0.44/0.66  thf('185', plain,
% 0.44/0.66      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66          != (sk_F)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66                = (sk_F))))),
% 0.44/0.66      inference('split', [status(esa)], ['141'])).
% 0.44/0.66  thf('186', plain,
% 0.44/0.66      (((((sk_F) != (sk_F))
% 0.44/0.66         | (v1_xboole_0 @ sk_D)
% 0.44/0.66         | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66         | (v1_xboole_0 @ sk_B)
% 0.44/0.66         | (v1_xboole_0 @ sk_A)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66                = (sk_F))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['184', '185'])).
% 0.44/0.66  thf('187', plain,
% 0.44/0.66      ((((v1_xboole_0 @ sk_A)
% 0.44/0.66         | (v1_xboole_0 @ sk_B)
% 0.44/0.66         | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66         | (v1_xboole_0 @ sk_D)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66                = (sk_F))))),
% 0.44/0.66      inference('simplify', [status(thm)], ['186'])).
% 0.44/0.66  thf('188', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('189', plain,
% 0.44/0.66      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66                = (sk_F))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['187', '188'])).
% 0.44/0.66  thf('190', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('191', plain,
% 0.44/0.66      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66                = (sk_F))))),
% 0.44/0.66      inference('clc', [status(thm)], ['189', '190'])).
% 0.44/0.66  thf('192', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('193', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_B))
% 0.44/0.66         <= (~
% 0.44/0.66             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66                = (sk_F))))),
% 0.44/0.66      inference('clc', [status(thm)], ['191', '192'])).
% 0.44/0.66  thf('194', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('195', plain,
% 0.44/0.66      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66          = (sk_F)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['193', '194'])).
% 0.44/0.66  thf('196', plain,
% 0.44/0.66      (~
% 0.44/0.66       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66          = (sk_E))) | 
% 0.44/0.66       ~
% 0.44/0.66       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.66          = (sk_F))) | 
% 0.44/0.66       ~
% 0.44/0.66       (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.66          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.66          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.66             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.44/0.66      inference('split', [status(esa)], ['141'])).
% 0.44/0.66  thf('197', plain,
% 0.44/0.66      (~
% 0.44/0.66       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66          = (sk_E)))),
% 0.44/0.66      inference('sat_resolution*', [status(thm)], ['156', '195', '196'])).
% 0.44/0.66  thf('198', plain,
% 0.44/0.66      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.66         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.66         != (sk_E))),
% 0.44/0.66      inference('simpl_trail', [status(thm)], ['142', '197'])).
% 0.44/0.66  thf('199', plain,
% 0.44/0.66      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['140', '198'])).
% 0.44/0.66  thf('200', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_D)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['15', '199'])).
% 0.44/0.66  thf('201', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_A)
% 0.44/0.66        | (v1_xboole_0 @ sk_B)
% 0.44/0.66        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.66        | (v1_xboole_0 @ sk_D))),
% 0.44/0.66      inference('simplify', [status(thm)], ['200'])).
% 0.44/0.66  thf('202', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('203', plain,
% 0.44/0.66      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['201', '202'])).
% 0.44/0.66  thf('204', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('205', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.66      inference('clc', [status(thm)], ['203', '204'])).
% 0.44/0.66  thf('206', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('207', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.66      inference('clc', [status(thm)], ['205', '206'])).
% 0.44/0.66  thf('208', plain, ($false), inference('demod', [status(thm)], ['0', '207'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
