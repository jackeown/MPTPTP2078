%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EisYlVR8wX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:04 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 793 expanded)
%              Number of leaves         :   40 ( 247 expanded)
%              Depth                    :   31
%              Number of atoms          : 3581 (30551 expanded)
%              Number of equality atoms :  114 ( 979 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_subset_1 @ X25 @ X26 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v4_relat_1 @ X13 @ X15 )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) )
      | ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) )
    | ( v4_relat_1 @ sk_E @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('81',plain,(
    v4_relat_1 @ sk_E @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('82',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('85',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('88',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('89',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X22 @ X20 ) @ X21 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['84','85'])).

thf('93',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X31 @ X32 @ X30 @ X33 )
        = ( k7_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v4_relat_1 @ X13 @ X15 )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) )
      | ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) )
    | ( v4_relat_1 @ sk_F @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('109',plain,(
    v4_relat_1 @ sk_F @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('114',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('117',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['112','113'])).

thf('119',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','93','94','95','100','119','120','121','122','123'])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
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
    inference('sup-',[status(thm)],['30','125'])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('132',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['128'])).

thf('133',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('135',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('139',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('140',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('141',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118'])).

thf('142',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141'])).

thf('143',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('145',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('146',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('147',plain,(
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

thf('148',plain,(
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
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
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
    inference('sup-',[status(thm)],['146','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('155',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('157',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('159',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('161',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118'])).

thf('162',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
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
    inference(demod,[status(thm)],['149','150','151','152','153','154','155','156','157','158','159','160','161','162','163','164','165'])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
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
    inference('sup-',[status(thm)],['145','167'])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
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
    inference('sup-',[status(thm)],['144','169'])).

thf('171',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['128'])).

thf('173',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['128'])).

thf('184',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['143','182','183'])).

thf('185',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['129','184'])).

thf('186',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['127','185'])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','186'])).

thf('188',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['0','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EisYlVR8wX
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 248 iterations in 0.236s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.70  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.70  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.70  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.70  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.45/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.70  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(t6_tmap_1, conjecture,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.70           ( ![C:$i]:
% 0.45/0.70             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.70                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.70               ( ![D:$i]:
% 0.45/0.70                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.70                   ( ( r1_subset_1 @ C @ D ) =>
% 0.45/0.70                     ( ![E:$i]:
% 0.45/0.70                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.70                           ( m1_subset_1 @
% 0.45/0.70                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.45/0.70                         ( ![F:$i]:
% 0.45/0.70                           ( ( ( v1_funct_1 @ F ) & 
% 0.45/0.70                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.70                               ( m1_subset_1 @
% 0.45/0.70                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.70                             ( ( ( k2_partfun1 @
% 0.45/0.70                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.45/0.70                                 ( k2_partfun1 @
% 0.45/0.70                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.45/0.70                               ( ( k2_partfun1 @
% 0.45/0.70                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.70                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.45/0.70                                 ( E ) ) & 
% 0.45/0.70                               ( ( k2_partfun1 @
% 0.45/0.70                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.70                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.45/0.70                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i]:
% 0.45/0.70        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.70          ( ![B:$i]:
% 0.45/0.70            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.70              ( ![C:$i]:
% 0.45/0.70                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.70                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.70                  ( ![D:$i]:
% 0.45/0.70                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.70                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.70                      ( ( r1_subset_1 @ C @ D ) =>
% 0.45/0.70                        ( ![E:$i]:
% 0.45/0.70                          ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.70                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.70                              ( m1_subset_1 @
% 0.45/0.70                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.45/0.70                            ( ![F:$i]:
% 0.45/0.70                              ( ( ( v1_funct_1 @ F ) & 
% 0.45/0.70                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.70                                  ( m1_subset_1 @
% 0.45/0.70                                    F @ 
% 0.45/0.70                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.70                                ( ( ( k2_partfun1 @
% 0.45/0.70                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.45/0.70                                    ( k2_partfun1 @
% 0.45/0.70                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.45/0.70                                  ( ( k2_partfun1 @
% 0.45/0.70                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.70                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.45/0.70                                    ( E ) ) & 
% 0.45/0.70                                  ( ( k2_partfun1 @
% 0.45/0.70                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.70                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.45/0.70                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.45/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(dt_k1_tmap_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.70         ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.70         ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.45/0.70         ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.45/0.70         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.70       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.45/0.70         ( v1_funct_2 @
% 0.45/0.70           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.70           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.45/0.70         ( m1_subset_1 @
% 0.45/0.70           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.70           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.45/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.45/0.70          | ~ (v1_funct_1 @ X41)
% 0.45/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.45/0.70          | (v1_xboole_0 @ X44)
% 0.45/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X45))
% 0.45/0.70          | (v1_xboole_0 @ X42)
% 0.45/0.70          | (v1_xboole_0 @ X43)
% 0.45/0.70          | (v1_xboole_0 @ X45)
% 0.45/0.70          | ~ (v1_funct_1 @ X46)
% 0.45/0.70          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.45/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46)))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.45/0.70  thf('5', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.45/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.70          | ~ (v1_funct_1 @ X0)
% 0.45/0.70          | (v1_xboole_0 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.45/0.70          | (v1_xboole_0 @ X1)
% 0.45/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.45/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.45/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.70          | ~ (v1_funct_1 @ X0)
% 0.45/0.70          | (v1_xboole_0 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.45/0.70          | (v1_xboole_0 @ X1)
% 0.45/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.45/0.70      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_D)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.45/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['2', '8'])).
% 0.45/0.70  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_D)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['1', '12'])).
% 0.45/0.70  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.70  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.45/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.45/0.70          | ~ (v1_funct_1 @ X41)
% 0.45/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.45/0.70          | (v1_xboole_0 @ X44)
% 0.45/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X45))
% 0.45/0.70          | (v1_xboole_0 @ X42)
% 0.45/0.70          | (v1_xboole_0 @ X43)
% 0.45/0.70          | (v1_xboole_0 @ X45)
% 0.45/0.70          | ~ (v1_funct_1 @ X46)
% 0.45/0.70          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.45/0.70          | (v1_funct_2 @ (k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46) @ 
% 0.45/0.70             (k4_subset_1 @ X45 @ X42 @ X44) @ X43))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.70           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.70          | ~ (v1_funct_1 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ X1)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.70  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.70           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.70          | ~ (v1_funct_1 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ X1)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_D)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.45/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.70          | (v1_funct_2 @ 
% 0.45/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['17', '23'])).
% 0.45/0.70  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_D)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | (v1_funct_2 @ 
% 0.45/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.45/0.70      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['16', '27'])).
% 0.45/0.70  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.70  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.45/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.45/0.70          | ~ (v1_funct_1 @ X41)
% 0.45/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.45/0.70          | (v1_xboole_0 @ X44)
% 0.45/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X45))
% 0.45/0.70          | (v1_xboole_0 @ X42)
% 0.45/0.70          | (v1_xboole_0 @ X43)
% 0.45/0.70          | (v1_xboole_0 @ X45)
% 0.45/0.70          | ~ (v1_funct_1 @ X46)
% 0.45/0.70          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.45/0.70          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.45/0.70          | (m1_subset_1 @ (k1_tmap_1 @ X45 @ X43 @ X42 @ X44 @ X41 @ X46) @ 
% 0.45/0.70             (k1_zfmisc_1 @ 
% 0.45/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X45 @ X42 @ X44) @ X43))))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.70          | ~ (v1_funct_1 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ X1)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.70  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.70          | ~ (v1_funct_1 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ X1)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.45/0.70  thf('39', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_D)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.45/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.70          | (m1_subset_1 @ 
% 0.45/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k1_zfmisc_1 @ 
% 0.45/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['32', '38'])).
% 0.45/0.70  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('42', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_D)
% 0.45/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.70          | (v1_xboole_0 @ sk_C)
% 0.45/0.70          | (v1_xboole_0 @ sk_B)
% 0.45/0.70          | (v1_xboole_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ 
% 0.45/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k1_zfmisc_1 @ 
% 0.45/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.45/0.70      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.45/0.70  thf('43', plain,
% 0.45/0.70      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70         (k1_zfmisc_1 @ 
% 0.45/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['31', '42'])).
% 0.45/0.70  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70         (k1_zfmisc_1 @ 
% 0.45/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.70  thf(d1_tmap_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.70           ( ![C:$i]:
% 0.45/0.70             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.70                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.70               ( ![D:$i]:
% 0.45/0.70                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.70                   ( ![E:$i]:
% 0.45/0.70                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.70                         ( m1_subset_1 @
% 0.45/0.70                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.45/0.70                       ( ![F:$i]:
% 0.45/0.70                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.70                             ( m1_subset_1 @
% 0.45/0.70                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.70                           ( ( ( k2_partfun1 @
% 0.45/0.70                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.45/0.70                               ( k2_partfun1 @
% 0.45/0.70                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.45/0.70                             ( ![G:$i]:
% 0.45/0.70                               ( ( ( v1_funct_1 @ G ) & 
% 0.45/0.70                                   ( v1_funct_2 @
% 0.45/0.70                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.45/0.70                                   ( m1_subset_1 @
% 0.45/0.70                                     G @ 
% 0.45/0.70                                     ( k1_zfmisc_1 @
% 0.45/0.70                                       ( k2_zfmisc_1 @
% 0.45/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.45/0.70                                 ( ( ( G ) =
% 0.45/0.70                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.45/0.70                                   ( ( ( k2_partfun1 @
% 0.45/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.45/0.70                                         C ) =
% 0.45/0.70                                       ( E ) ) & 
% 0.45/0.70                                     ( ( k2_partfun1 @
% 0.45/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.45/0.70                                         D ) =
% 0.45/0.70                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf('46', plain,
% 0.45/0.70      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.70         ((v1_xboole_0 @ X34)
% 0.45/0.70          | (v1_xboole_0 @ X35)
% 0.45/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.45/0.70          | ~ (v1_funct_1 @ X37)
% 0.45/0.70          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.45/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.45/0.70          | ((X40) != (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 0.45/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ X40 @ X39)
% 0.45/0.70              = (X38))
% 0.45/0.70          | ~ (m1_subset_1 @ X40 @ 
% 0.45/0.70               (k1_zfmisc_1 @ 
% 0.45/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 0.45/0.70          | ~ (v1_funct_2 @ X40 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 0.45/0.70          | ~ (v1_funct_1 @ X40)
% 0.45/0.70          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 0.45/0.70              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 0.45/0.70                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 0.45/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 0.45/0.70          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 0.45/0.70          | ~ (v1_funct_1 @ X38)
% 0.45/0.70          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 0.45/0.70          | (v1_xboole_0 @ X39)
% 0.45/0.70          | (v1_xboole_0 @ X36))),
% 0.45/0.70      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.45/0.70  thf('47', plain,
% 0.45/0.70      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.70         ((v1_xboole_0 @ X36)
% 0.45/0.70          | (v1_xboole_0 @ X39)
% 0.45/0.70          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 0.45/0.70          | ~ (v1_funct_1 @ X38)
% 0.45/0.70          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 0.45/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 0.45/0.70          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 0.45/0.70              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 0.45/0.70                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 0.45/0.70          | ~ (v1_funct_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 0.45/0.70          | ~ (v1_funct_2 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 0.45/0.70               (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 0.45/0.70          | ~ (m1_subset_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 0.45/0.70               (k1_zfmisc_1 @ 
% 0.45/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 0.45/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ 
% 0.45/0.70              (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ X39) = (
% 0.45/0.70              X38))
% 0.45/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.45/0.70          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.45/0.70          | ~ (v1_funct_1 @ X37)
% 0.45/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.45/0.70          | (v1_xboole_0 @ X35)
% 0.45/0.70          | (v1_xboole_0 @ X34))),
% 0.45/0.70      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.70  thf('48', plain,
% 0.45/0.70      (((v1_xboole_0 @ sk_D)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_D)
% 0.45/0.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.70        | ~ (v1_funct_1 @ sk_F)
% 0.45/0.70        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.70        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70            = (sk_E))
% 0.45/0.70        | ~ (v1_funct_2 @ 
% 0.45/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.70        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.70            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.45/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.45/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.45/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.45/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['45', '47'])).
% 0.45/0.70  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('52', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(redefinition_k9_subset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.70       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.70  thf('54', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.70         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.45/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.45/0.70  thf('55', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.70  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(redefinition_r1_subset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.45/0.70       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.45/0.70  thf('57', plain,
% 0.45/0.70      (![X25 : $i, X26 : $i]:
% 0.45/0.70         ((v1_xboole_0 @ X25)
% 0.45/0.70          | (v1_xboole_0 @ X26)
% 0.45/0.70          | (r1_xboole_0 @ X25 @ X26)
% 0.45/0.70          | ~ (r1_subset_1 @ X25 @ X26))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.45/0.70  thf('58', plain,
% 0.45/0.70      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.45/0.70        | (v1_xboole_0 @ sk_D)
% 0.45/0.70        | (v1_xboole_0 @ sk_C))),
% 0.45/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.70  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.70      inference('clc', [status(thm)], ['58', '59'])).
% 0.45/0.70  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.45/0.70      inference('clc', [status(thm)], ['60', '61'])).
% 0.45/0.70  thf(d7_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.70       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.70  thf('63', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.70  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('65', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(redefinition_k2_partfun1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.70     ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.70       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.45/0.70  thf('66', plain,
% 0.45/0.70      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.45/0.70          | ~ (v1_funct_1 @ X30)
% 0.45/0.70          | ((k2_partfun1 @ X31 @ X32 @ X30 @ X33) = (k7_relat_1 @ X30 @ X33)))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.45/0.70  thf('67', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.45/0.70          | ~ (v1_funct_1 @ sk_E))),
% 0.45/0.70      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.70  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('69', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.70  thf(d10_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.70  thf('70', plain,
% 0.45/0.70      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.70  thf('71', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.45/0.70      inference('simplify', [status(thm)], ['70'])).
% 0.45/0.70  thf(d18_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ B ) =>
% 0.45/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.70  thf('72', plain,
% 0.45/0.70      (![X16 : $i, X17 : $i]:
% 0.45/0.70         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.45/0.70          | (v4_relat_1 @ X16 @ X17)
% 0.45/0.70          | ~ (v1_relat_1 @ X16))),
% 0.45/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.70  thf('73', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.70  thf('74', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(cc5_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.70       ( ![C:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 0.45/0.70  thf('75', plain,
% 0.45/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.45/0.70          | (v4_relat_1 @ X13 @ X15)
% 0.45/0.70          | ~ (v4_relat_1 @ X14 @ X15)
% 0.45/0.70          | ~ (v1_relat_1 @ X14))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.45/0.70  thf('76', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))
% 0.45/0.70          | ~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B) @ X0)
% 0.45/0.70          | (v4_relat_1 @ sk_E @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.70  thf(fc6_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.70  thf('77', plain,
% 0.45/0.70      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.70  thf('78', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B) @ X0)
% 0.45/0.70          | (v4_relat_1 @ sk_E @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['76', '77'])).
% 0.45/0.70  thf('79', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))
% 0.45/0.70        | (v4_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['73', '78'])).
% 0.45/0.70  thf('80', plain,
% 0.45/0.70      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.70  thf('81', plain,
% 0.45/0.70      ((v4_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('demod', [status(thm)], ['79', '80'])).
% 0.45/0.70  thf(t209_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.45/0.70  thf('82', plain,
% 0.45/0.70      (![X23 : $i, X24 : $i]:
% 0.45/0.70         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.45/0.70          | ~ (v4_relat_1 @ X23 @ X24)
% 0.45/0.70          | ~ (v1_relat_1 @ X23))),
% 0.45/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.70  thf('83', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ sk_E)
% 0.45/0.70        | ((sk_E)
% 0.45/0.70            = (k7_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.70  thf('84', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(cc1_relset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( v1_relat_1 @ C ) ))).
% 0.45/0.70  thf('85', plain,
% 0.45/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.70         ((v1_relat_1 @ X27)
% 0.45/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.70  thf('86', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.70      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.70  thf('87', plain,
% 0.45/0.70      (((sk_E)
% 0.45/0.70         = (k7_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.45/0.70      inference('demod', [status(thm)], ['83', '86'])).
% 0.45/0.70  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.70  thf('88', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.70  thf(t207_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ C ) =>
% 0.45/0.70       ( ( r1_xboole_0 @ A @ B ) =>
% 0.45/0.70         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.70  thf('89', plain,
% 0.45/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.70         (~ (r1_xboole_0 @ X20 @ X21)
% 0.45/0.70          | ~ (v1_relat_1 @ X22)
% 0.45/0.70          | ((k7_relat_1 @ (k7_relat_1 @ X22 @ X20) @ X21) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.45/0.70  thf('90', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.70  thf('91', plain,
% 0.45/0.70      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.70        | ~ (v1_relat_1 @ sk_E))),
% 0.45/0.70      inference('sup+', [status(thm)], ['87', '90'])).
% 0.45/0.70  thf('92', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.70      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.70  thf('93', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.70  thf('94', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.70  thf('95', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('96', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('97', plain,
% 0.45/0.70      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.45/0.70          | ~ (v1_funct_1 @ X30)
% 0.45/0.70          | ((k2_partfun1 @ X31 @ X32 @ X30 @ X33) = (k7_relat_1 @ X30 @ X33)))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.45/0.70  thf('98', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.45/0.70          | ~ (v1_funct_1 @ sk_F))),
% 0.45/0.70      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.70  thf('99', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('100', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['98', '99'])).
% 0.45/0.70  thf('101', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.70  thf('102', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('103', plain,
% 0.45/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.45/0.70          | (v4_relat_1 @ X13 @ X15)
% 0.45/0.70          | ~ (v4_relat_1 @ X14 @ X15)
% 0.45/0.70          | ~ (v1_relat_1 @ X14))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.45/0.70  thf('104', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))
% 0.45/0.70          | ~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B) @ X0)
% 0.45/0.70          | (v4_relat_1 @ sk_F @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['102', '103'])).
% 0.45/0.70  thf('105', plain,
% 0.45/0.70      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.70  thf('106', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B) @ X0)
% 0.45/0.70          | (v4_relat_1 @ sk_F @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['104', '105'])).
% 0.45/0.70  thf('107', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))
% 0.45/0.70        | (v4_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['101', '106'])).
% 0.45/0.70  thf('108', plain,
% 0.45/0.70      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.70  thf('109', plain,
% 0.45/0.70      ((v4_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('demod', [status(thm)], ['107', '108'])).
% 0.45/0.70  thf('110', plain,
% 0.45/0.70      (![X23 : $i, X24 : $i]:
% 0.45/0.70         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.45/0.70          | ~ (v4_relat_1 @ X23 @ X24)
% 0.45/0.70          | ~ (v1_relat_1 @ X23))),
% 0.45/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.70  thf('111', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ sk_F)
% 0.45/0.70        | ((sk_F)
% 0.45/0.70            = (k7_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['109', '110'])).
% 0.45/0.70  thf('112', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('113', plain,
% 0.45/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.70         ((v1_relat_1 @ X27)
% 0.45/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.70  thf('114', plain, ((v1_relat_1 @ sk_F)),
% 0.45/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.70  thf('115', plain,
% 0.45/0.70      (((sk_F)
% 0.45/0.70         = (k7_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))))),
% 0.45/0.70      inference('demod', [status(thm)], ['111', '114'])).
% 0.45/0.70  thf('116', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.70  thf('117', plain,
% 0.45/0.70      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.70        | ~ (v1_relat_1 @ sk_F))),
% 0.45/0.70      inference('sup+', [status(thm)], ['115', '116'])).
% 0.45/0.70  thf('118', plain, ((v1_relat_1 @ sk_F)),
% 0.45/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.70  thf('119', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['117', '118'])).
% 0.45/0.70  thf('120', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('121', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('122', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('123', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('124', plain,
% 0.45/0.70      (((v1_xboole_0 @ sk_D)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_D)
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70            = (sk_E))
% 0.45/0.70        | ~ (v1_funct_2 @ 
% 0.45/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.70        | ((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_A))),
% 0.45/0.70      inference('demod', [status(thm)],
% 0.45/0.70                ['48', '49', '50', '51', '52', '55', '64', '69', '93', '94', 
% 0.45/0.70                 '95', '100', '119', '120', '121', '122', '123'])).
% 0.45/0.70  thf('125', plain,
% 0.45/0.70      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.70        | ~ (v1_funct_2 @ 
% 0.45/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70            = (sk_E))
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('simplify', [status(thm)], ['124'])).
% 0.45/0.70  thf('126', plain,
% 0.45/0.70      (((v1_xboole_0 @ sk_D)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_D)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70            = (sk_E))
% 0.45/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['30', '125'])).
% 0.45/0.70  thf('127', plain,
% 0.45/0.70      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70            = (sk_E))
% 0.45/0.70        | (v1_xboole_0 @ sk_A)
% 0.45/0.70        | (v1_xboole_0 @ sk_B)
% 0.45/0.70        | (v1_xboole_0 @ sk_C)
% 0.45/0.70        | (v1_xboole_0 @ sk_D))),
% 0.45/0.70      inference('simplify', [status(thm)], ['126'])).
% 0.45/0.70  thf('128', plain,
% 0.45/0.70      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70            != (sk_E))
% 0.45/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.70            != (sk_F)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('129', plain,
% 0.45/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70          != (sk_E)))
% 0.45/0.70         <= (~
% 0.45/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.70                = (sk_E))))),
% 0.45/0.70      inference('split', [status(esa)], ['128'])).
% 0.45/0.70  thf('130', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['98', '99'])).
% 0.45/0.70  thf('131', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.70  thf('132', plain,
% 0.45/0.70      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.45/0.70         <= (~
% 0.45/0.70             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.70      inference('split', [status(esa)], ['128'])).
% 0.45/0.70  thf('133', plain,
% 0.45/0.70      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.45/0.70         <= (~
% 0.45/0.70             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['131', '132'])).
% 0.45/0.70  thf('134', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.70  thf('135', plain,
% 0.45/0.70      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.45/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.45/0.70         <= (~
% 0.45/0.70             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.70      inference('demod', [status(thm)], ['133', '134'])).
% 0.45/0.70  thf('136', plain,
% 0.45/0.70      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.45/0.70          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.45/0.70         <= (~
% 0.45/0.70             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['130', '135'])).
% 0.45/0.70  thf('137', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('138', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.70  thf('139', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.70  thf('140', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('141', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['117', '118'])).
% 0.45/0.70  thf('142', plain,
% 0.45/0.70      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.70         <= (~
% 0.45/0.70             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.70      inference('demod', [status(thm)],
% 0.45/0.70                ['136', '137', '138', '139', '140', '141'])).
% 0.45/0.70  thf('143', plain,
% 0.45/0.70      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.70          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.70             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['142'])).
% 0.45/0.70  thf('144', plain,
% 0.45/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.53/0.70  thf('145', plain,
% 0.53/0.70      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.53/0.70         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.53/0.70  thf('146', plain,
% 0.53/0.70      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.53/0.70         (k1_zfmisc_1 @ 
% 0.53/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.53/0.70  thf('147', plain,
% 0.53/0.70      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.53/0.70         ((v1_xboole_0 @ X34)
% 0.53/0.70          | (v1_xboole_0 @ X35)
% 0.53/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.53/0.70          | ~ (v1_funct_1 @ X37)
% 0.53/0.70          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.53/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.53/0.70          | ((X40) != (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 0.53/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ X40 @ X35)
% 0.53/0.70              = (X37))
% 0.53/0.70          | ~ (m1_subset_1 @ X40 @ 
% 0.53/0.70               (k1_zfmisc_1 @ 
% 0.53/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 0.53/0.70          | ~ (v1_funct_2 @ X40 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 0.53/0.70          | ~ (v1_funct_1 @ X40)
% 0.53/0.70          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 0.53/0.70              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 0.53/0.70                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 0.53/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 0.53/0.70          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 0.53/0.70          | ~ (v1_funct_1 @ X38)
% 0.53/0.70          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 0.53/0.70          | (v1_xboole_0 @ X39)
% 0.53/0.70          | (v1_xboole_0 @ X36))),
% 0.53/0.70      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.53/0.70  thf('148', plain,
% 0.53/0.70      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.53/0.70         ((v1_xboole_0 @ X36)
% 0.53/0.70          | (v1_xboole_0 @ X39)
% 0.53/0.70          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X36))
% 0.53/0.70          | ~ (v1_funct_1 @ X38)
% 0.53/0.70          | ~ (v1_funct_2 @ X38 @ X39 @ X34)
% 0.53/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X34)))
% 0.53/0.70          | ((k2_partfun1 @ X39 @ X34 @ X38 @ (k9_subset_1 @ X36 @ X39 @ X35))
% 0.53/0.70              != (k2_partfun1 @ X35 @ X34 @ X37 @ 
% 0.53/0.70                  (k9_subset_1 @ X36 @ X39 @ X35)))
% 0.53/0.70          | ~ (v1_funct_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37))
% 0.53/0.70          | ~ (v1_funct_2 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 0.53/0.70               (k4_subset_1 @ X36 @ X39 @ X35) @ X34)
% 0.53/0.70          | ~ (m1_subset_1 @ (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ 
% 0.53/0.70               (k1_zfmisc_1 @ 
% 0.53/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34)))
% 0.53/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X36 @ X39 @ X35) @ X34 @ 
% 0.53/0.70              (k1_tmap_1 @ X36 @ X34 @ X39 @ X35 @ X38 @ X37) @ X35) = (
% 0.53/0.70              X37))
% 0.53/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.53/0.70          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.53/0.70          | ~ (v1_funct_1 @ X37)
% 0.53/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.53/0.70          | (v1_xboole_0 @ X35)
% 0.53/0.70          | (v1_xboole_0 @ X34))),
% 0.53/0.70      inference('simplify', [status(thm)], ['147'])).
% 0.53/0.70  thf('149', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_D)
% 0.53/0.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.53/0.70        | ~ (v1_funct_1 @ sk_F)
% 0.53/0.70        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.53/0.70        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.53/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70            = (sk_F))
% 0.53/0.70        | ~ (v1_funct_2 @ 
% 0.53/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.53/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.53/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.53/0.70        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.53/0.70            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.53/0.70            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.53/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.53/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.53/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.53/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.53/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_A))),
% 0.53/0.70      inference('sup-', [status(thm)], ['146', '148'])).
% 0.53/0.70  thf('150', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('151', plain, ((v1_funct_1 @ sk_F)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('152', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('153', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('154', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.53/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.70  thf('155', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.53/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.70  thf('156', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.53/0.70      inference('demod', [status(thm)], ['67', '68'])).
% 0.53/0.70  thf('157', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.53/0.70  thf('158', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.53/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.70  thf('159', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.53/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.70  thf('160', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.53/0.70      inference('demod', [status(thm)], ['98', '99'])).
% 0.53/0.70  thf('161', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.70      inference('demod', [status(thm)], ['117', '118'])).
% 0.53/0.70  thf('162', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('163', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('164', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('165', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('166', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_D)
% 0.53/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70            = (sk_F))
% 0.53/0.70        | ~ (v1_funct_2 @ 
% 0.53/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.53/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.53/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.53/0.70        | ((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_A))),
% 0.53/0.70      inference('demod', [status(thm)],
% 0.53/0.70                ['149', '150', '151', '152', '153', '154', '155', '156', 
% 0.53/0.70                 '157', '158', '159', '160', '161', '162', '163', '164', '165'])).
% 0.53/0.70  thf('167', plain,
% 0.53/0.70      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.53/0.70        | ~ (v1_funct_2 @ 
% 0.53/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.53/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.53/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70            = (sk_F))
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('simplify', [status(thm)], ['166'])).
% 0.53/0.70  thf('168', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70            = (sk_F))
% 0.53/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['145', '167'])).
% 0.53/0.70  thf('169', plain,
% 0.53/0.70      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.53/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70            = (sk_F))
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('simplify', [status(thm)], ['168'])).
% 0.53/0.70  thf('170', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70            = (sk_F)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['144', '169'])).
% 0.53/0.70  thf('171', plain,
% 0.53/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70          = (sk_F))
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('simplify', [status(thm)], ['170'])).
% 0.53/0.70  thf('172', plain,
% 0.53/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70          != (sk_F)))
% 0.53/0.70         <= (~
% 0.53/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70                = (sk_F))))),
% 0.53/0.70      inference('split', [status(esa)], ['128'])).
% 0.53/0.70  thf('173', plain,
% 0.53/0.70      (((((sk_F) != (sk_F))
% 0.53/0.70         | (v1_xboole_0 @ sk_D)
% 0.53/0.70         | (v1_xboole_0 @ sk_C)
% 0.53/0.70         | (v1_xboole_0 @ sk_B)
% 0.53/0.70         | (v1_xboole_0 @ sk_A)))
% 0.53/0.70         <= (~
% 0.53/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70                = (sk_F))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['171', '172'])).
% 0.53/0.70  thf('174', plain,
% 0.53/0.70      ((((v1_xboole_0 @ sk_A)
% 0.53/0.70         | (v1_xboole_0 @ sk_B)
% 0.53/0.70         | (v1_xboole_0 @ sk_C)
% 0.53/0.70         | (v1_xboole_0 @ sk_D)))
% 0.53/0.70         <= (~
% 0.53/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70                = (sk_F))))),
% 0.53/0.70      inference('simplify', [status(thm)], ['173'])).
% 0.53/0.70  thf('175', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('176', plain,
% 0.53/0.70      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.53/0.70         <= (~
% 0.53/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70                = (sk_F))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['174', '175'])).
% 0.53/0.70  thf('177', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('178', plain,
% 0.53/0.70      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.53/0.70         <= (~
% 0.53/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70                = (sk_F))))),
% 0.53/0.70      inference('clc', [status(thm)], ['176', '177'])).
% 0.53/0.70  thf('179', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('180', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_B))
% 0.53/0.70         <= (~
% 0.53/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70                = (sk_F))))),
% 0.53/0.70      inference('clc', [status(thm)], ['178', '179'])).
% 0.53/0.70  thf('181', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('182', plain,
% 0.53/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70          = (sk_F)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['180', '181'])).
% 0.53/0.70  thf('183', plain,
% 0.53/0.70      (~
% 0.53/0.70       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.53/0.70          = (sk_E))) | 
% 0.53/0.70       ~
% 0.53/0.70       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.53/0.70          = (sk_F))) | 
% 0.53/0.70       ~
% 0.53/0.70       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.53/0.70          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.53/0.70             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.53/0.70      inference('split', [status(esa)], ['128'])).
% 0.53/0.70  thf('184', plain,
% 0.53/0.70      (~
% 0.53/0.70       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.53/0.70          = (sk_E)))),
% 0.53/0.70      inference('sat_resolution*', [status(thm)], ['143', '182', '183'])).
% 0.53/0.70  thf('185', plain,
% 0.53/0.70      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.53/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.53/0.70         != (sk_E))),
% 0.53/0.70      inference('simpl_trail', [status(thm)], ['129', '184'])).
% 0.53/0.70  thf('186', plain,
% 0.53/0.70      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('simplify_reflect-', [status(thm)], ['127', '185'])).
% 0.53/0.70  thf('187', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_D)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_A))),
% 0.53/0.70      inference('sup-', [status(thm)], ['15', '186'])).
% 0.53/0.70  thf('188', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_A)
% 0.53/0.70        | (v1_xboole_0 @ sk_B)
% 0.53/0.70        | (v1_xboole_0 @ sk_C)
% 0.53/0.70        | (v1_xboole_0 @ sk_D))),
% 0.53/0.70      inference('simplify', [status(thm)], ['187'])).
% 0.53/0.70  thf('189', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('190', plain,
% 0.53/0.70      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.53/0.70      inference('sup-', [status(thm)], ['188', '189'])).
% 0.53/0.70  thf('191', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('192', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.53/0.70      inference('clc', [status(thm)], ['190', '191'])).
% 0.53/0.70  thf('193', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('194', plain, ((v1_xboole_0 @ sk_B)),
% 0.53/0.70      inference('clc', [status(thm)], ['192', '193'])).
% 0.53/0.70  thf('195', plain, ($false), inference('demod', [status(thm)], ['0', '194'])).
% 0.53/0.70  
% 0.53/0.70  % SZS output end Refutation
% 0.53/0.70  
% 0.53/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
