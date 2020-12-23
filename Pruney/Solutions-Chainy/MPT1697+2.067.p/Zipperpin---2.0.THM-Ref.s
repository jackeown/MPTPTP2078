%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a6wIgt1f1D

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:03 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  237 ( 793 expanded)
%              Number of leaves         :   40 ( 247 expanded)
%              Depth                    :   29
%              Number of atoms          : 3597 (30567 expanded)
%              Number of equality atoms :  116 ( 981 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45 ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45 ) @ ( k4_subset_1 @ X44 @ X41 @ X43 ) @ X42 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X44 @ X41 @ X43 ) @ X42 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( X39
       != ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 @ X39 @ X38 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 )
      | ~ ( v1_funct_1 @ X39 )
      | ( ( k2_partfun1 @ X38 @ X33 @ X37 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) )
       != ( k2_partfun1 @ X34 @ X33 @ X36 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X33 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X33 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X33 ) ) )
      | ( ( k2_partfun1 @ X38 @ X33 @ X37 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) )
       != ( k2_partfun1 @ X34 @ X33 @ X36 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) @ X38 )
        = X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_subset_1 @ X24 @ X25 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 )
        = ( k7_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v4_relat_1 @ X12 @ X14 )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X21 @ X19 ) @ X20 )
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 )
        = ( k7_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v4_relat_1 @ X12 @ X14 )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) )
      | ~ ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) @ X0 )
      | ( v4_relat_1 @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('109',plain,(
    v4_relat_1 @ sk_F @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ~ ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E ) ),
    inference('sup-',[status(thm)],['15','127'])).

thf('129',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('134',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('135',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('137',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('139',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('142',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('143',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118'])).

thf('144',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('147',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('148',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('149',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( X39
       != ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 @ X39 @ X34 )
        = X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 )
      | ~ ( v1_funct_1 @ X39 )
      | ( ( k2_partfun1 @ X38 @ X33 @ X37 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) )
       != ( k2_partfun1 @ X34 @ X33 @ X36 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X33 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('150',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X33 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X33 ) ) )
      | ( ( k2_partfun1 @ X38 @ X33 @ X37 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) )
       != ( k2_partfun1 @ X34 @ X33 @ X36 @ ( k9_subset_1 @ X35 @ X38 @ X34 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X35 @ X38 @ X34 ) @ X33 @ ( k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36 ) @ X34 )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
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
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('157',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('159',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('161',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('163',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','118'])).

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
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156','157','158','159','160','161','162','163','164','165','166','167'])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
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
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['147','169'])).

thf('171',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
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
    inference('sup-',[status(thm)],['146','171'])).

thf('173',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['130'])).

thf('175',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('186',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['145','184','185'])).

thf('187',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['131','186'])).

thf('188',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['129','187'])).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a6wIgt1f1D
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:52:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 178 iterations in 0.226s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.74  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.52/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.74  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(sk_F_type, type, sk_F: $i).
% 0.52/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.74  thf(sk_E_type, type, sk_E: $i).
% 0.52/0.74  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.52/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.74  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.74  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.74  thf(t6_tmap_1, conjecture,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.74       ( ![B:$i]:
% 0.52/0.74         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.74           ( ![C:$i]:
% 0.52/0.74             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.74                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.74               ( ![D:$i]:
% 0.52/0.74                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.74                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.74                   ( ( r1_subset_1 @ C @ D ) =>
% 0.52/0.74                     ( ![E:$i]:
% 0.52/0.74                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.74                           ( m1_subset_1 @
% 0.52/0.74                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.52/0.74                         ( ![F:$i]:
% 0.52/0.74                           ( ( ( v1_funct_1 @ F ) & 
% 0.52/0.74                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.74                               ( m1_subset_1 @
% 0.52/0.74                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.74                             ( ( ( k2_partfun1 @
% 0.52/0.74                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.52/0.74                                 ( k2_partfun1 @
% 0.52/0.74                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.52/0.74                               ( ( k2_partfun1 @
% 0.52/0.74                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.74                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.52/0.74                                 ( E ) ) & 
% 0.52/0.74                               ( ( k2_partfun1 @
% 0.52/0.74                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.74                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.52/0.74                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i]:
% 0.52/0.74        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.74          ( ![B:$i]:
% 0.52/0.74            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.74              ( ![C:$i]:
% 0.52/0.74                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.74                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.74                  ( ![D:$i]:
% 0.52/0.74                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.74                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.74                      ( ( r1_subset_1 @ C @ D ) =>
% 0.52/0.74                        ( ![E:$i]:
% 0.52/0.74                          ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.74                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.74                              ( m1_subset_1 @
% 0.52/0.74                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.52/0.74                            ( ![F:$i]:
% 0.52/0.74                              ( ( ( v1_funct_1 @ F ) & 
% 0.52/0.74                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.74                                  ( m1_subset_1 @
% 0.52/0.74                                    F @ 
% 0.52/0.74                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.74                                ( ( ( k2_partfun1 @
% 0.52/0.74                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.52/0.74                                    ( k2_partfun1 @
% 0.52/0.74                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.52/0.74                                  ( ( k2_partfun1 @
% 0.52/0.74                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.74                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.52/0.74                                    ( E ) ) & 
% 0.52/0.74                                  ( ( k2_partfun1 @
% 0.52/0.74                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.74                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.52/0.74                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.52/0.74  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('2', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(dt_k1_tmap_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.52/0.74         ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.52/0.74         ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.52/0.74         ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.74         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.52/0.74         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.74         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.74       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.52/0.74         ( v1_funct_2 @
% 0.52/0.74           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.52/0.74           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.52/0.74         ( m1_subset_1 @
% 0.52/0.74           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.52/0.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.52/0.74          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.52/0.74          | ~ (v1_funct_1 @ X40)
% 0.52/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.52/0.74          | (v1_xboole_0 @ X43)
% 0.52/0.74          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X44))
% 0.52/0.74          | (v1_xboole_0 @ X41)
% 0.52/0.74          | (v1_xboole_0 @ X42)
% 0.52/0.74          | (v1_xboole_0 @ X44)
% 0.52/0.74          | ~ (v1_funct_1 @ X45)
% 0.52/0.74          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.52/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.52/0.74          | (v1_funct_1 @ (k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45)))),
% 0.52/0.74      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.52/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.52/0.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | (v1_xboole_0 @ X2)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.52/0.74          | (v1_xboole_0 @ X1)
% 0.52/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.52/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.74  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.52/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.52/0.74          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.52/0.74          | ~ (v1_funct_1 @ X0)
% 0.52/0.74          | (v1_xboole_0 @ X2)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.52/0.74          | (v1_xboole_0 @ X1)
% 0.52/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.74      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.52/0.74  thf('9', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_D)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ sk_F)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.74          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['2', '8'])).
% 0.52/0.74  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_D)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.52/0.74      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.52/0.74  thf('13', plain,
% 0.52/0.74      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['1', '12'])).
% 0.52/0.74  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('15', plain,
% 0.52/0.74      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.74  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('17', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('18', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('19', plain,
% 0.52/0.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.52/0.74          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.52/0.74          | ~ (v1_funct_1 @ X40)
% 0.52/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.52/0.74          | (v1_xboole_0 @ X43)
% 0.52/0.74          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X44))
% 0.52/0.74          | (v1_xboole_0 @ X41)
% 0.52/0.74          | (v1_xboole_0 @ X42)
% 0.52/0.74          | (v1_xboole_0 @ X44)
% 0.52/0.74          | ~ (v1_funct_1 @ X45)
% 0.52/0.74          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.52/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.52/0.74          | (v1_funct_2 @ (k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45) @ 
% 0.52/0.74             (k4_subset_1 @ X44 @ X41 @ X43) @ X42))),
% 0.52/0.74      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.52/0.74  thf('20', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.52/0.74           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.52/0.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.74          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.74          | ~ (v1_funct_1 @ X2)
% 0.52/0.74          | (v1_xboole_0 @ X1)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.74  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('23', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.52/0.74           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.52/0.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.74          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.74          | ~ (v1_funct_1 @ X2)
% 0.52/0.74          | (v1_xboole_0 @ X1)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.52/0.74      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.52/0.74  thf('24', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_D)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ sk_F)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.74          | (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['17', '23'])).
% 0.52/0.74  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('27', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_D)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.52/0.74      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.52/0.74  thf('28', plain,
% 0.52/0.74      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['16', '27'])).
% 0.52/0.74  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('30', plain,
% 0.52/0.74      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('demod', [status(thm)], ['28', '29'])).
% 0.52/0.74  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('32', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('33', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('34', plain,
% 0.52/0.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.52/0.74          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.52/0.74          | ~ (v1_funct_1 @ X40)
% 0.52/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.52/0.74          | (v1_xboole_0 @ X43)
% 0.52/0.74          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X44))
% 0.52/0.74          | (v1_xboole_0 @ X41)
% 0.52/0.74          | (v1_xboole_0 @ X42)
% 0.52/0.74          | (v1_xboole_0 @ X44)
% 0.52/0.74          | ~ (v1_funct_1 @ X45)
% 0.52/0.74          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.52/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.52/0.74          | (m1_subset_1 @ (k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45) @ 
% 0.52/0.74             (k1_zfmisc_1 @ 
% 0.52/0.74              (k2_zfmisc_1 @ (k4_subset_1 @ X44 @ X41 @ X43) @ X42))))),
% 0.52/0.74      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.52/0.74  thf('35', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.52/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.52/0.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.74          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.74          | ~ (v1_funct_1 @ X2)
% 0.52/0.74          | (v1_xboole_0 @ X1)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.74  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('38', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.52/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.52/0.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.74          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.74          | ~ (v1_funct_1 @ X2)
% 0.52/0.74          | (v1_xboole_0 @ X1)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.52/0.74      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.52/0.74  thf('39', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_D)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | ~ (v1_funct_1 @ sk_F)
% 0.52/0.74          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.74          | (m1_subset_1 @ 
% 0.52/0.74             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k1_zfmisc_1 @ 
% 0.52/0.74              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['32', '38'])).
% 0.52/0.74  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('42', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_D)
% 0.52/0.74          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.52/0.74          | (v1_xboole_0 @ sk_C)
% 0.52/0.74          | (v1_xboole_0 @ sk_B)
% 0.52/0.74          | (v1_xboole_0 @ X0)
% 0.52/0.74          | (m1_subset_1 @ 
% 0.52/0.74             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k1_zfmisc_1 @ 
% 0.52/0.74              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.52/0.74      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.52/0.74  thf('43', plain,
% 0.52/0.74      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74         (k1_zfmisc_1 @ 
% 0.52/0.74          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['31', '42'])).
% 0.52/0.74  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('45', plain,
% 0.52/0.74      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74         (k1_zfmisc_1 @ 
% 0.52/0.74          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.52/0.74  thf(d1_tmap_1, axiom,
% 0.52/0.74    (![A:$i]:
% 0.52/0.74     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.74       ( ![B:$i]:
% 0.52/0.74         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.74           ( ![C:$i]:
% 0.52/0.74             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.74                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.74               ( ![D:$i]:
% 0.52/0.74                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.74                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.74                   ( ![E:$i]:
% 0.52/0.74                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.74                         ( m1_subset_1 @
% 0.52/0.74                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.52/0.74                       ( ![F:$i]:
% 0.52/0.74                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.74                             ( m1_subset_1 @
% 0.52/0.74                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.74                           ( ( ( k2_partfun1 @
% 0.52/0.74                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.52/0.74                               ( k2_partfun1 @
% 0.52/0.74                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.52/0.74                             ( ![G:$i]:
% 0.52/0.74                               ( ( ( v1_funct_1 @ G ) & 
% 0.52/0.74                                   ( v1_funct_2 @
% 0.52/0.74                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.52/0.74                                   ( m1_subset_1 @
% 0.52/0.74                                     G @ 
% 0.52/0.74                                     ( k1_zfmisc_1 @
% 0.52/0.74                                       ( k2_zfmisc_1 @
% 0.52/0.74                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.52/0.74                                 ( ( ( G ) =
% 0.52/0.74                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.52/0.74                                   ( ( ( k2_partfun1 @
% 0.52/0.74                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.52/0.74                                         C ) =
% 0.52/0.74                                       ( E ) ) & 
% 0.52/0.74                                     ( ( k2_partfun1 @
% 0.52/0.74                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.52/0.74                                         D ) =
% 0.52/0.74                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf('46', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.52/0.74         ((v1_xboole_0 @ X33)
% 0.52/0.74          | (v1_xboole_0 @ X34)
% 0.52/0.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | ~ (v1_funct_1 @ X36)
% 0.52/0.74          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.52/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.52/0.74          | ((X39) != (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.52/0.74          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ X39 @ X38)
% 0.52/0.74              = (X37))
% 0.52/0.74          | ~ (m1_subset_1 @ X39 @ 
% 0.52/0.74               (k1_zfmisc_1 @ 
% 0.52/0.74                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.52/0.74          | ~ (v1_funct_2 @ X39 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.52/0.74          | ~ (v1_funct_1 @ X39)
% 0.52/0.74          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.52/0.74              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.52/0.74                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.52/0.74          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.52/0.74          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.52/0.74          | ~ (v1_funct_1 @ X37)
% 0.52/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | (v1_xboole_0 @ X38)
% 0.52/0.74          | (v1_xboole_0 @ X35))),
% 0.52/0.74      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.52/0.74  thf('47', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.52/0.74         ((v1_xboole_0 @ X35)
% 0.52/0.74          | (v1_xboole_0 @ X38)
% 0.52/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | ~ (v1_funct_1 @ X37)
% 0.52/0.74          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.52/0.74          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.52/0.74          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.52/0.74              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.52/0.74                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.52/0.74          | ~ (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.52/0.74          | ~ (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.52/0.74               (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.52/0.74          | ~ (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.52/0.74               (k1_zfmisc_1 @ 
% 0.52/0.74                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.52/0.74          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ 
% 0.52/0.74              (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ X38) = (
% 0.52/0.74              X37))
% 0.52/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.52/0.74          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.52/0.74          | ~ (v1_funct_1 @ X36)
% 0.52/0.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | (v1_xboole_0 @ X34)
% 0.52/0.74          | (v1_xboole_0 @ X33))),
% 0.52/0.74      inference('simplify', [status(thm)], ['46'])).
% 0.52/0.74  thf('48', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | ~ (v1_funct_1 @ sk_F)
% 0.52/0.74        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            = (sk_E))
% 0.52/0.74        | ~ (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.52/0.74        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.52/0.74        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['45', '47'])).
% 0.52/0.74  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('52', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(redefinition_k9_subset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.74       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.74  thf('54', plain,
% 0.52/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.74         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.52/0.74          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.74  thf('55', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.74  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(redefinition_r1_subset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.52/0.74       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.52/0.74  thf('57', plain,
% 0.52/0.74      (![X24 : $i, X25 : $i]:
% 0.52/0.74         ((v1_xboole_0 @ X24)
% 0.52/0.74          | (v1_xboole_0 @ X25)
% 0.52/0.74          | (r1_xboole_0 @ X24 @ X25)
% 0.52/0.74          | ~ (r1_subset_1 @ X24 @ X25))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.52/0.74  thf('58', plain,
% 0.52/0.74      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C))),
% 0.52/0.74      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.74  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.52/0.74      inference('clc', [status(thm)], ['58', '59'])).
% 0.52/0.74  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.52/0.74      inference('clc', [status(thm)], ['60', '61'])).
% 0.52/0.74  thf(d7_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.52/0.74       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.74  thf('63', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.74  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('65', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(redefinition_k2_partfun1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.74     ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.74       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.52/0.74  thf('66', plain,
% 0.52/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.52/0.74          | ~ (v1_funct_1 @ X29)
% 0.52/0.74          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.52/0.74  thf('67', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.52/0.74          | ~ (v1_funct_1 @ sk_E))),
% 0.52/0.74      inference('sup-', [status(thm)], ['65', '66'])).
% 0.52/0.74  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('69', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.74  thf(d10_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.74  thf('70', plain,
% 0.52/0.74      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('71', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.52/0.74      inference('simplify', [status(thm)], ['70'])).
% 0.52/0.74  thf(d18_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ B ) =>
% 0.52/0.74       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.74  thf('72', plain,
% 0.52/0.74      (![X15 : $i, X16 : $i]:
% 0.52/0.74         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.52/0.74          | (v4_relat_1 @ X15 @ X16)
% 0.52/0.74          | ~ (v1_relat_1 @ X15))),
% 0.52/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.74  thf('73', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.74  thf('74', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(cc5_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.74       ( ![C:$i]:
% 0.52/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 0.52/0.74  thf('75', plain,
% 0.52/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.52/0.74          | (v4_relat_1 @ X12 @ X14)
% 0.52/0.74          | ~ (v4_relat_1 @ X13 @ X14)
% 0.52/0.74          | ~ (v1_relat_1 @ X13))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.52/0.74  thf('76', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))
% 0.52/0.74          | ~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B) @ X0)
% 0.52/0.74          | (v4_relat_1 @ sk_E @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['74', '75'])).
% 0.52/0.74  thf(fc6_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.74  thf('77', plain,
% 0.52/0.74      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.52/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.74  thf('78', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B) @ X0)
% 0.52/0.74          | (v4_relat_1 @ sk_E @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['76', '77'])).
% 0.52/0.74  thf('79', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))
% 0.52/0.74        | (v4_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['73', '78'])).
% 0.52/0.74  thf('80', plain,
% 0.52/0.74      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.52/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.74  thf('81', plain,
% 0.52/0.74      ((v4_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('demod', [status(thm)], ['79', '80'])).
% 0.52/0.74  thf(t209_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.74  thf('82', plain,
% 0.52/0.74      (![X22 : $i, X23 : $i]:
% 0.52/0.74         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.52/0.74          | ~ (v4_relat_1 @ X22 @ X23)
% 0.52/0.74          | ~ (v1_relat_1 @ X22))),
% 0.52/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.74  thf('83', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_E)
% 0.52/0.74        | ((sk_E)
% 0.52/0.74            = (k7_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['81', '82'])).
% 0.52/0.74  thf('84', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(cc1_relset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.74       ( v1_relat_1 @ C ) ))).
% 0.52/0.74  thf('85', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.74         ((v1_relat_1 @ X26)
% 0.52/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.74  thf('86', plain, ((v1_relat_1 @ sk_E)),
% 0.52/0.74      inference('sup-', [status(thm)], ['84', '85'])).
% 0.52/0.74  thf('87', plain,
% 0.52/0.74      (((sk_E)
% 0.52/0.74         = (k7_relat_1 @ sk_E @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 0.52/0.74      inference('demod', [status(thm)], ['83', '86'])).
% 0.52/0.74  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.52/0.74  thf('88', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.52/0.74      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.74  thf(t207_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ C ) =>
% 0.52/0.74       ( ( r1_xboole_0 @ A @ B ) =>
% 0.52/0.74         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.74  thf('89', plain,
% 0.52/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.74         (~ (r1_xboole_0 @ X19 @ X20)
% 0.52/0.74          | ~ (v1_relat_1 @ X21)
% 0.52/0.74          | ((k7_relat_1 @ (k7_relat_1 @ X21 @ X19) @ X20) = (k1_xboole_0)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.52/0.74  thf('90', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.74          | ~ (v1_relat_1 @ X1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['88', '89'])).
% 0.52/0.74  thf('91', plain,
% 0.52/0.74      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_E))),
% 0.52/0.74      inference('sup+', [status(thm)], ['87', '90'])).
% 0.52/0.74  thf('92', plain, ((v1_relat_1 @ sk_E)),
% 0.52/0.74      inference('sup-', [status(thm)], ['84', '85'])).
% 0.52/0.74  thf('93', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['91', '92'])).
% 0.52/0.74  thf('94', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.74  thf('95', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('96', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('97', plain,
% 0.52/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.52/0.74          | ~ (v1_funct_1 @ X29)
% 0.52/0.74          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.52/0.74  thf('98', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.52/0.74          | ~ (v1_funct_1 @ sk_F))),
% 0.52/0.74      inference('sup-', [status(thm)], ['96', '97'])).
% 0.52/0.74  thf('99', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('100', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['98', '99'])).
% 0.52/0.74  thf('101', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.74  thf('102', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('103', plain,
% 0.52/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.52/0.74          | (v4_relat_1 @ X12 @ X14)
% 0.52/0.74          | ~ (v4_relat_1 @ X13 @ X14)
% 0.52/0.74          | ~ (v1_relat_1 @ X13))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.52/0.74  thf('104', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))
% 0.52/0.74          | ~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B) @ X0)
% 0.52/0.74          | (v4_relat_1 @ sk_F @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['102', '103'])).
% 0.52/0.74  thf('105', plain,
% 0.52/0.74      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.52/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.74  thf('106', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         (~ (v4_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B) @ X0)
% 0.52/0.74          | (v4_relat_1 @ sk_F @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['104', '105'])).
% 0.52/0.74  thf('107', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))
% 0.52/0.74        | (v4_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['101', '106'])).
% 0.52/0.74  thf('108', plain,
% 0.52/0.74      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.52/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.74  thf('109', plain,
% 0.52/0.74      ((v4_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('demod', [status(thm)], ['107', '108'])).
% 0.52/0.74  thf('110', plain,
% 0.52/0.74      (![X22 : $i, X23 : $i]:
% 0.52/0.74         (((X22) = (k7_relat_1 @ X22 @ X23))
% 0.52/0.74          | ~ (v4_relat_1 @ X22 @ X23)
% 0.52/0.74          | ~ (v1_relat_1 @ X22))),
% 0.52/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.74  thf('111', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_F)
% 0.52/0.74        | ((sk_F)
% 0.52/0.74            = (k7_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['109', '110'])).
% 0.52/0.74  thf('112', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('113', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.74         ((v1_relat_1 @ X26)
% 0.52/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.74  thf('114', plain, ((v1_relat_1 @ sk_F)),
% 0.52/0.74      inference('sup-', [status(thm)], ['112', '113'])).
% 0.52/0.74  thf('115', plain,
% 0.52/0.74      (((sk_F)
% 0.52/0.74         = (k7_relat_1 @ sk_F @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B))))),
% 0.52/0.74      inference('demod', [status(thm)], ['111', '114'])).
% 0.52/0.74  thf('116', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.74          | ~ (v1_relat_1 @ X1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['88', '89'])).
% 0.52/0.74  thf('117', plain,
% 0.52/0.74      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_F))),
% 0.52/0.74      inference('sup+', [status(thm)], ['115', '116'])).
% 0.52/0.74  thf('118', plain, ((v1_relat_1 @ sk_F)),
% 0.52/0.74      inference('sup-', [status(thm)], ['112', '113'])).
% 0.52/0.74  thf('119', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['117', '118'])).
% 0.52/0.74  thf('120', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('121', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('122', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('123', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('124', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            = (sk_E))
% 0.52/0.74        | ~ (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)],
% 0.52/0.74                ['48', '49', '50', '51', '52', '55', '64', '69', '93', '94', 
% 0.52/0.74                 '95', '100', '119', '120', '121', '122', '123'])).
% 0.52/0.74  thf('125', plain,
% 0.52/0.74      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ~ (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            = (sk_E))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify', [status(thm)], ['124'])).
% 0.52/0.74  thf('126', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            = (sk_E))
% 0.52/0.74        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['30', '125'])).
% 0.52/0.74  thf('127', plain,
% 0.52/0.74      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            = (sk_E))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify', [status(thm)], ['126'])).
% 0.52/0.74  thf('128', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            = (sk_E)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['15', '127'])).
% 0.52/0.74  thf('129', plain,
% 0.52/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74          = (sk_E))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify', [status(thm)], ['128'])).
% 0.52/0.74  thf('130', plain,
% 0.52/0.74      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74            != (sk_E))
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            != (sk_F)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('131', plain,
% 0.52/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74          != (sk_E)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74                = (sk_E))))),
% 0.52/0.74      inference('split', [status(esa)], ['130'])).
% 0.52/0.74  thf('132', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['98', '99'])).
% 0.52/0.74  thf('133', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.74  thf('134', plain,
% 0.52/0.74      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.52/0.74      inference('split', [status(esa)], ['130'])).
% 0.52/0.74  thf('135', plain,
% 0.52/0.74      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['133', '134'])).
% 0.52/0.74  thf('136', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.74  thf('137', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('138', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('139', plain,
% 0.52/0.74      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.52/0.74          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.52/0.74      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.52/0.74  thf('140', plain,
% 0.52/0.74      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.52/0.74          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['132', '139'])).
% 0.52/0.74  thf('141', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.74  thf('142', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['91', '92'])).
% 0.52/0.74  thf('143', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['117', '118'])).
% 0.52/0.74  thf('144', plain,
% 0.52/0.74      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.52/0.74      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.52/0.74  thf('145', plain,
% 0.52/0.74      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['144'])).
% 0.52/0.74  thf('146', plain,
% 0.52/0.74      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.74  thf('147', plain,
% 0.52/0.74      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('demod', [status(thm)], ['28', '29'])).
% 0.52/0.74  thf('148', plain,
% 0.52/0.74      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74         (k1_zfmisc_1 @ 
% 0.52/0.74          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.52/0.74  thf('149', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.52/0.74         ((v1_xboole_0 @ X33)
% 0.52/0.74          | (v1_xboole_0 @ X34)
% 0.52/0.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | ~ (v1_funct_1 @ X36)
% 0.52/0.74          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.52/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.52/0.74          | ((X39) != (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.52/0.74          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ X39 @ X34)
% 0.52/0.74              = (X36))
% 0.52/0.74          | ~ (m1_subset_1 @ X39 @ 
% 0.52/0.74               (k1_zfmisc_1 @ 
% 0.52/0.74                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.52/0.74          | ~ (v1_funct_2 @ X39 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.52/0.74          | ~ (v1_funct_1 @ X39)
% 0.52/0.74          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.52/0.74              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.52/0.74                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.52/0.74          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.52/0.74          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.52/0.74          | ~ (v1_funct_1 @ X37)
% 0.52/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | (v1_xboole_0 @ X38)
% 0.52/0.74          | (v1_xboole_0 @ X35))),
% 0.52/0.74      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.52/0.74  thf('150', plain,
% 0.52/0.74      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.52/0.74         ((v1_xboole_0 @ X35)
% 0.52/0.74          | (v1_xboole_0 @ X38)
% 0.52/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | ~ (v1_funct_1 @ X37)
% 0.52/0.74          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.52/0.74          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.52/0.74          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.52/0.74              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.52/0.74                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.52/0.74          | ~ (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.52/0.74          | ~ (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.52/0.74               (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.52/0.74          | ~ (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.52/0.74               (k1_zfmisc_1 @ 
% 0.52/0.74                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.52/0.74          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ 
% 0.52/0.74              (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ X34) = (
% 0.52/0.74              X36))
% 0.52/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.52/0.74          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.52/0.74          | ~ (v1_funct_1 @ X36)
% 0.52/0.74          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.52/0.74          | (v1_xboole_0 @ X34)
% 0.52/0.74          | (v1_xboole_0 @ X33))),
% 0.52/0.74      inference('simplify', [status(thm)], ['149'])).
% 0.52/0.74  thf('151', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | ~ (v1_funct_1 @ sk_F)
% 0.52/0.74        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            = (sk_F))
% 0.52/0.74        | ~ (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.52/0.74            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.52/0.74        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.52/0.74        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.52/0.74        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.74        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['148', '150'])).
% 0.52/0.74  thf('152', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('153', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('154', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('155', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('156', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.74  thf('157', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('158', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.74  thf('159', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['91', '92'])).
% 0.52/0.74  thf('160', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.74  thf('161', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.74  thf('162', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.52/0.74      inference('demod', [status(thm)], ['98', '99'])).
% 0.52/0.74  thf('163', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.74      inference('demod', [status(thm)], ['117', '118'])).
% 0.52/0.74  thf('164', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('165', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('166', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('167', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('168', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            = (sk_F))
% 0.52/0.74        | ~ (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)],
% 0.52/0.74                ['151', '152', '153', '154', '155', '156', '157', '158', 
% 0.52/0.74                 '159', '160', '161', '162', '163', '164', '165', '166', '167'])).
% 0.52/0.74  thf('169', plain,
% 0.52/0.74      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ~ (v1_funct_2 @ 
% 0.52/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.74             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            = (sk_F))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify', [status(thm)], ['168'])).
% 0.52/0.74  thf('170', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            = (sk_F))
% 0.52/0.74        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['147', '169'])).
% 0.52/0.74  thf('171', plain,
% 0.52/0.74      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            = (sk_F))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify', [status(thm)], ['170'])).
% 0.52/0.74  thf('172', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_D)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74            = (sk_F)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['146', '171'])).
% 0.52/0.74  thf('173', plain,
% 0.52/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74          = (sk_F))
% 0.52/0.74        | (v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify', [status(thm)], ['172'])).
% 0.52/0.74  thf('174', plain,
% 0.52/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74          != (sk_F)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74                = (sk_F))))),
% 0.52/0.74      inference('split', [status(esa)], ['130'])).
% 0.52/0.74  thf('175', plain,
% 0.52/0.74      (((((sk_F) != (sk_F))
% 0.52/0.74         | (v1_xboole_0 @ sk_D)
% 0.52/0.74         | (v1_xboole_0 @ sk_C)
% 0.52/0.74         | (v1_xboole_0 @ sk_B)
% 0.52/0.74         | (v1_xboole_0 @ sk_A)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74                = (sk_F))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['173', '174'])).
% 0.52/0.74  thf('176', plain,
% 0.52/0.74      ((((v1_xboole_0 @ sk_A)
% 0.52/0.74         | (v1_xboole_0 @ sk_B)
% 0.52/0.74         | (v1_xboole_0 @ sk_C)
% 0.52/0.74         | (v1_xboole_0 @ sk_D)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74                = (sk_F))))),
% 0.52/0.74      inference('simplify', [status(thm)], ['175'])).
% 0.52/0.74  thf('177', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('178', plain,
% 0.52/0.74      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74                = (sk_F))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['176', '177'])).
% 0.52/0.74  thf('179', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('180', plain,
% 0.52/0.74      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74                = (sk_F))))),
% 0.52/0.74      inference('clc', [status(thm)], ['178', '179'])).
% 0.52/0.74  thf('181', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('182', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_B))
% 0.52/0.74         <= (~
% 0.52/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74                = (sk_F))))),
% 0.52/0.74      inference('clc', [status(thm)], ['180', '181'])).
% 0.52/0.74  thf('183', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('184', plain,
% 0.52/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74          = (sk_F)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['182', '183'])).
% 0.52/0.74  thf('185', plain,
% 0.52/0.74      (~
% 0.52/0.74       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74          = (sk_E))) | 
% 0.52/0.74       ~
% 0.52/0.74       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.74          = (sk_F))) | 
% 0.52/0.74       ~
% 0.52/0.74       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.52/0.74          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.74             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.52/0.74      inference('split', [status(esa)], ['130'])).
% 0.52/0.74  thf('186', plain,
% 0.52/0.74      (~
% 0.52/0.74       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74          = (sk_E)))),
% 0.52/0.74      inference('sat_resolution*', [status(thm)], ['145', '184', '185'])).
% 0.52/0.74  thf('187', plain,
% 0.52/0.74      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.52/0.74         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.52/0.74         != (sk_E))),
% 0.52/0.74      inference('simpl_trail', [status(thm)], ['131', '186'])).
% 0.52/0.74  thf('188', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_A)
% 0.52/0.74        | (v1_xboole_0 @ sk_B)
% 0.52/0.74        | (v1_xboole_0 @ sk_C)
% 0.52/0.74        | (v1_xboole_0 @ sk_D))),
% 0.52/0.74      inference('simplify_reflect-', [status(thm)], ['129', '187'])).
% 0.52/0.74  thf('189', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('190', plain,
% 0.52/0.74      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['188', '189'])).
% 0.52/0.74  thf('191', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('192', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.52/0.74      inference('clc', [status(thm)], ['190', '191'])).
% 0.52/0.74  thf('193', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('194', plain, ((v1_xboole_0 @ sk_B)),
% 0.52/0.74      inference('clc', [status(thm)], ['192', '193'])).
% 0.52/0.74  thf('195', plain, ($false), inference('demod', [status(thm)], ['0', '194'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
