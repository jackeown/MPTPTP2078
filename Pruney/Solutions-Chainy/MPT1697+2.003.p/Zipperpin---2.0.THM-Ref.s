%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8butAw4FUN

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:53 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  256 ( 934 expanded)
%              Number of leaves         :   43 ( 292 expanded)
%              Depth                    :   31
%              Number of atoms          : 3695 (35716 expanded)
%              Number of equality atoms :  129 (1231 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['62','63'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('75',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('77',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['89','90'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('92',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('95',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('96',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('98',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('99',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['93','96','99'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('101',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k7_relat_1 @ X14 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['94','95'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('107',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('108',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('114',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('126',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['123','126','129'])).

thf('131',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k7_relat_1 @ X14 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['124','125'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','57','68','73','105','106','107','112','135','136','137','138','139'])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
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
    inference('sup-',[status(thm)],['30','141'])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('148',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['144'])).

thf('149',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('151',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('152',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('153',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('156',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','104'])).

thf('157',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','134'])).

thf('158',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('161',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('163',plain,(
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

thf('164',plain,(
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
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
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
    inference('sup-',[status(thm)],['162','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('171',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('173',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','104'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('175',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','67'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('177',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','134'])).

thf('178',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
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
    inference(demod,[status(thm)],['165','166','167','168','169','170','171','172','173','174','175','176','177','178','179','180','181'])).

thf('183',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
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
    inference('sup-',[status(thm)],['161','183'])).

thf('185',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
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
    inference('sup-',[status(thm)],['160','185'])).

thf('187',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['144'])).

thf('189',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['144'])).

thf('200',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['159','198','199'])).

thf('201',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['145','200'])).

thf('202',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['143','201'])).

thf('203',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','202'])).

thf('204',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['208','209'])).

thf('211',plain,(
    $false ),
    inference(demod,[status(thm)],['0','210'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8butAw4FUN
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 191 iterations in 0.157s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.61  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(t6_tmap_1, conjecture,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.61           ( ![C:$i]:
% 0.44/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61               ( ![D:$i]:
% 0.44/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61                   ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.61                     ( ![E:$i]:
% 0.44/0.61                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.61                           ( m1_subset_1 @
% 0.44/0.61                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.61                         ( ![F:$i]:
% 0.44/0.61                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.61                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.61                               ( m1_subset_1 @
% 0.44/0.61                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.61                             ( ( ( k2_partfun1 @
% 0.44/0.61                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.61                                 ( k2_partfun1 @
% 0.44/0.61                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.61                               ( ( k2_partfun1 @
% 0.44/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.61                                 ( E ) ) & 
% 0.44/0.61                               ( ( k2_partfun1 @
% 0.44/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.61                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i]:
% 0.44/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.61          ( ![B:$i]:
% 0.44/0.61            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.61              ( ![C:$i]:
% 0.44/0.61                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.61                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61                  ( ![D:$i]:
% 0.44/0.61                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.61                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61                      ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.61                        ( ![E:$i]:
% 0.44/0.61                          ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.61                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.61                              ( m1_subset_1 @
% 0.44/0.61                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.61                            ( ![F:$i]:
% 0.44/0.61                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.61                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.61                                  ( m1_subset_1 @
% 0.44/0.61                                    F @ 
% 0.44/0.61                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.61                                ( ( ( k2_partfun1 @
% 0.44/0.61                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.61                                    ( k2_partfun1 @
% 0.44/0.61                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.61                                  ( ( k2_partfun1 @
% 0.44/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.61                                    ( E ) ) & 
% 0.44/0.61                                  ( ( k2_partfun1 @
% 0.44/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.61                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.44/0.61  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(dt_k1_tmap_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.61         ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.44/0.61         ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.44/0.61         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.61       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.61         ( v1_funct_2 @
% 0.44/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.61           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.61         ( m1_subset_1 @
% 0.44/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.44/0.61          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X39)
% 0.44/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.44/0.61          | (v1_xboole_0 @ X42)
% 0.44/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.44/0.61          | (v1_xboole_0 @ X40)
% 0.44/0.61          | (v1_xboole_0 @ X41)
% 0.44/0.61          | (v1_xboole_0 @ X43)
% 0.44/0.61          | ~ (v1_funct_1 @ X44)
% 0.44/0.61          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.44/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.44/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44)))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.61          | ~ (v1_funct_1 @ X0)
% 0.44/0.61          | (v1_xboole_0 @ X2)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.61          | (v1_xboole_0 @ X1)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.61  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.61          | ~ (v1_funct_1 @ X0)
% 0.44/0.61          | (v1_xboole_0 @ X2)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.61          | (v1_xboole_0 @ X1)
% 0.44/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.61      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_D)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.61  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_D)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['1', '12'])).
% 0.44/0.61  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.44/0.61          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X39)
% 0.44/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.44/0.61          | (v1_xboole_0 @ X42)
% 0.44/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.44/0.61          | (v1_xboole_0 @ X40)
% 0.44/0.61          | (v1_xboole_0 @ X41)
% 0.44/0.61          | (v1_xboole_0 @ X43)
% 0.44/0.61          | ~ (v1_funct_1 @ X44)
% 0.44/0.61          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.44/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.44/0.61          | (v1_funct_2 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.44/0.61             (k4_subset_1 @ X43 @ X40 @ X42) @ X41))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.61           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.61          | ~ (v1_funct_1 @ X2)
% 0.44/0.61          | (v1_xboole_0 @ X1)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.61  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.61           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.61          | ~ (v1_funct_1 @ X2)
% 0.44/0.61          | (v1_xboole_0 @ X1)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_D)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.61          | (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.61      inference('sup-', [status(thm)], ['17', '23'])).
% 0.44/0.61  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_D)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.61      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '27'])).
% 0.44/0.61  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.44/0.61          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X39)
% 0.44/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.44/0.61          | (v1_xboole_0 @ X42)
% 0.44/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.44/0.61          | (v1_xboole_0 @ X40)
% 0.44/0.61          | (v1_xboole_0 @ X41)
% 0.44/0.61          | (v1_xboole_0 @ X43)
% 0.44/0.61          | ~ (v1_funct_1 @ X44)
% 0.44/0.61          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.44/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.44/0.61          | (m1_subset_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.44/0.61             (k1_zfmisc_1 @ 
% 0.44/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X43 @ X40 @ X42) @ X41))))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.61          | ~ (v1_funct_1 @ X2)
% 0.44/0.61          | (v1_xboole_0 @ X1)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.61  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.61          | ~ (v1_funct_1 @ X2)
% 0.44/0.61          | (v1_xboole_0 @ X1)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.61      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.44/0.61  thf('39', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_D)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.61          | (m1_subset_1 @ 
% 0.44/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k1_zfmisc_1 @ 
% 0.44/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['32', '38'])).
% 0.44/0.61  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_D)
% 0.44/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.61          | (v1_xboole_0 @ sk_C)
% 0.44/0.61          | (v1_xboole_0 @ sk_B)
% 0.44/0.61          | (v1_xboole_0 @ X0)
% 0.44/0.61          | (m1_subset_1 @ 
% 0.44/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k1_zfmisc_1 @ 
% 0.44/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61         (k1_zfmisc_1 @ 
% 0.44/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['31', '42'])).
% 0.44/0.61  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61         (k1_zfmisc_1 @ 
% 0.44/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.61  thf(d1_tmap_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.61           ( ![C:$i]:
% 0.44/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61               ( ![D:$i]:
% 0.44/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.61                   ( ![E:$i]:
% 0.44/0.61                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.61                         ( m1_subset_1 @
% 0.44/0.61                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.61                       ( ![F:$i]:
% 0.44/0.61                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.61                             ( m1_subset_1 @
% 0.44/0.61                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.61                           ( ( ( k2_partfun1 @
% 0.44/0.61                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.61                               ( k2_partfun1 @
% 0.44/0.61                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.44/0.61                             ( ![G:$i]:
% 0.44/0.61                               ( ( ( v1_funct_1 @ G ) & 
% 0.44/0.61                                   ( v1_funct_2 @
% 0.44/0.61                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.61                                   ( m1_subset_1 @
% 0.44/0.61                                     G @ 
% 0.44/0.61                                     ( k1_zfmisc_1 @
% 0.44/0.61                                       ( k2_zfmisc_1 @
% 0.44/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.44/0.61                                 ( ( ( G ) =
% 0.44/0.61                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.61                                   ( ( ( k2_partfun1 @
% 0.44/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.61                                         C ) =
% 0.44/0.61                                       ( E ) ) & 
% 0.44/0.61                                     ( ( k2_partfun1 @
% 0.44/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.61                                         D ) =
% 0.44/0.61                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X32)
% 0.44/0.61          | (v1_xboole_0 @ X33)
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.61          | ~ (v1_funct_1 @ X35)
% 0.44/0.61          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.61          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X37)
% 0.44/0.61              = (X36))
% 0.44/0.61          | ~ (m1_subset_1 @ X38 @ 
% 0.44/0.61               (k1_zfmisc_1 @ 
% 0.44/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.61          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.61          | ~ (v1_funct_1 @ X38)
% 0.44/0.61          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.61              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.61                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.61          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.61          | ~ (v1_funct_1 @ X36)
% 0.44/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.61          | (v1_xboole_0 @ X37)
% 0.44/0.61          | (v1_xboole_0 @ X34))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X34)
% 0.44/0.61          | (v1_xboole_0 @ X37)
% 0.44/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.61          | ~ (v1_funct_1 @ X36)
% 0.44/0.61          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.61          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.61              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.61                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.61               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.61               (k1_zfmisc_1 @ 
% 0.44/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.44/0.61              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X37) = (
% 0.44/0.61              X36))
% 0.44/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.61          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.61          | ~ (v1_funct_1 @ X35)
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.61          | (v1_xboole_0 @ X33)
% 0.44/0.61          | (v1_xboole_0 @ X32))),
% 0.44/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.61  thf('48', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            = (sk_E))
% 0.44/0.61        | ~ (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.61            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.61        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['45', '47'])).
% 0.44/0.61  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('52', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.61  thf('54', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.61         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.44/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.61  thf(t12_setfam_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.61  thf('56', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.61         (((k9_subset_1 @ X8 @ X6 @ X7) = (k1_setfam_1 @ (k2_tarski @ X6 @ X7)))
% 0.44/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.44/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.44/0.61  thf('57', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D)
% 0.44/0.61           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_D)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '56'])).
% 0.44/0.61  thf('58', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.61       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.61  thf('59', plain,
% 0.44/0.61      (![X15 : $i, X16 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X15)
% 0.44/0.61          | (v1_xboole_0 @ X16)
% 0.44/0.61          | (r1_xboole_0 @ X15 @ X16)
% 0.44/0.61          | ~ (r1_subset_1 @ X15 @ X16))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.61  thf('60', plain,
% 0.44/0.61      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.44/0.61  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('62', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.61      inference('clc', [status(thm)], ['60', '61'])).
% 0.44/0.61  thf('63', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('64', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.44/0.61      inference('clc', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf(d7_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.61  thf('65', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.61  thf('66', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.61  thf('67', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (k1_xboole_0))
% 0.44/0.61          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.44/0.61  thf('68', plain,
% 0.44/0.61      (((k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['64', '67'])).
% 0.44/0.61  thf('69', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.61  thf('70', plain,
% 0.44/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.44/0.61          | ~ (v1_funct_1 @ X28)
% 0.44/0.61          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.61  thf('71', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.44/0.61  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('73', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.61  thf(commutativity_k2_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.44/0.61  thf('74', plain,
% 0.44/0.61      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.44/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.61  thf(t2_boole, axiom,
% 0.44/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.61  thf('75', plain,
% 0.44/0.61      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.61  thf('76', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.61  thf('77', plain,
% 0.44/0.61      (![X3 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X3 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['75', '76'])).
% 0.44/0.61  thf('78', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['74', '77'])).
% 0.44/0.61  thf('79', plain,
% 0.44/0.61      (![X0 : $i, X2 : $i]:
% 0.44/0.61         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.61  thf('80', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]:
% 0.44/0.61         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.61  thf('81', plain,
% 0.44/0.61      (![X0 : $i, X2 : $i]:
% 0.44/0.61         ((r1_xboole_0 @ X0 @ X2)
% 0.44/0.61          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X2)) != (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.44/0.61  thf('82', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['78', '81'])).
% 0.44/0.61  thf('83', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['82'])).
% 0.44/0.61  thf('84', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc5_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.61       ( ![C:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.61  thf('85', plain,
% 0.44/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.44/0.61          | (v1_partfun1 @ X23 @ X24)
% 0.44/0.61          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.44/0.61          | ~ (v1_funct_1 @ X23)
% 0.44/0.61          | (v1_xboole_0 @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.61  thf('86', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.61        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.61  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('88', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('89', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.44/0.61  thf('90', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('91', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.44/0.61      inference('clc', [status(thm)], ['89', '90'])).
% 0.44/0.61  thf(d4_partfun1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.61       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.61  thf('92', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i]:
% 0.44/0.61         (~ (v1_partfun1 @ X27 @ X26)
% 0.44/0.61          | ((k1_relat_1 @ X27) = (X26))
% 0.44/0.61          | ~ (v4_relat_1 @ X27 @ X26)
% 0.44/0.61          | ~ (v1_relat_1 @ X27))),
% 0.44/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.61  thf('93', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ sk_E)
% 0.44/0.61        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.44/0.61        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.61  thf('94', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( v1_relat_1 @ C ) ))).
% 0.44/0.61  thf('95', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.61         ((v1_relat_1 @ X17)
% 0.44/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.61  thf('96', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.61      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.61  thf('97', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc2_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.61  thf('98', plain,
% 0.44/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.61         ((v4_relat_1 @ X20 @ X21)
% 0.44/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.61  thf('99', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.44/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.44/0.61  thf('100', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['93', '96', '99'])).
% 0.44/0.61  thf(t187_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.61           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.61  thf('101', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X13 @ (k1_relat_1 @ X14))
% 0.44/0.61          | ((k7_relat_1 @ X14 @ X13) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X14))),
% 0.44/0.61      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.61  thf('102', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_E)
% 0.44/0.61          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['100', '101'])).
% 0.44/0.61  thf('103', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.61      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.61  thf('104', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.61          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.44/0.61  thf('105', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['83', '104'])).
% 0.44/0.61  thf('106', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D)
% 0.44/0.61           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_D)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '56'])).
% 0.44/0.61  thf('107', plain,
% 0.44/0.61      (((k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['64', '67'])).
% 0.44/0.61  thf('108', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('109', plain,
% 0.44/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.44/0.61          | ~ (v1_funct_1 @ X28)
% 0.44/0.61          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.61  thf('110', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.61      inference('sup-', [status(thm)], ['108', '109'])).
% 0.44/0.61  thf('111', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('112', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['110', '111'])).
% 0.44/0.61  thf('113', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['82'])).
% 0.44/0.61  thf('114', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('115', plain,
% 0.44/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.44/0.61          | (v1_partfun1 @ X23 @ X24)
% 0.44/0.61          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.44/0.61          | ~ (v1_funct_1 @ X23)
% 0.44/0.61          | (v1_xboole_0 @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.61  thf('116', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.61        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['114', '115'])).
% 0.44/0.61  thf('117', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('118', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('119', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.44/0.61  thf('120', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('121', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.44/0.61      inference('clc', [status(thm)], ['119', '120'])).
% 0.44/0.61  thf('122', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i]:
% 0.44/0.61         (~ (v1_partfun1 @ X27 @ X26)
% 0.44/0.61          | ((k1_relat_1 @ X27) = (X26))
% 0.44/0.61          | ~ (v4_relat_1 @ X27 @ X26)
% 0.44/0.61          | ~ (v1_relat_1 @ X27))),
% 0.44/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.61  thf('123', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ sk_F)
% 0.44/0.61        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.44/0.61        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['121', '122'])).
% 0.44/0.61  thf('124', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('125', plain,
% 0.44/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.61         ((v1_relat_1 @ X17)
% 0.44/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.61  thf('126', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.61      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.61  thf('127', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('128', plain,
% 0.44/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.61         ((v4_relat_1 @ X20 @ X21)
% 0.44/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.61  thf('129', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.44/0.61      inference('sup-', [status(thm)], ['127', '128'])).
% 0.44/0.61  thf('130', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['123', '126', '129'])).
% 0.44/0.61  thf('131', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X13 @ (k1_relat_1 @ X14))
% 0.44/0.61          | ((k7_relat_1 @ X14 @ X13) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X14))),
% 0.44/0.61      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.61  thf('132', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_F)
% 0.44/0.61          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['130', '131'])).
% 0.44/0.61  thf('133', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.61      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.61  thf('134', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.61          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['132', '133'])).
% 0.44/0.61  thf('135', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['113', '134'])).
% 0.44/0.61  thf('136', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('137', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('138', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('139', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('140', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            = (sk_E))
% 0.44/0.61        | ~ (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)],
% 0.44/0.61                ['48', '49', '50', '51', '52', '57', '68', '73', '105', '106', 
% 0.44/0.61                 '107', '112', '135', '136', '137', '138', '139'])).
% 0.44/0.61  thf('141', plain,
% 0.44/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ~ (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            = (sk_E))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['140'])).
% 0.44/0.61  thf('142', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            = (sk_E))
% 0.44/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '141'])).
% 0.44/0.61  thf('143', plain,
% 0.44/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            = (sk_E))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['142'])).
% 0.44/0.61  thf('144', plain,
% 0.44/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            != (sk_E))
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            != (sk_F)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('145', plain,
% 0.44/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61          != (sk_E)))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62                = (sk_E))))),
% 0.44/0.62      inference('split', [status(esa)], ['144'])).
% 0.44/0.62  thf('146', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['110', '111'])).
% 0.44/0.62  thf('147', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D)
% 0.44/0.62           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['53', '56'])).
% 0.44/0.62  thf('148', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('split', [status(esa)], ['144'])).
% 0.44/0.62  thf('149', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62              (k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['147', '148'])).
% 0.44/0.62  thf('150', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D)
% 0.44/0.62           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['53', '56'])).
% 0.44/0.62  thf('151', plain,
% 0.44/0.62      (((k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['64', '67'])).
% 0.44/0.62  thf('152', plain,
% 0.44/0.62      (((k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['64', '67'])).
% 0.44/0.62  thf('153', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.44/0.62  thf('154', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.62          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['146', '153'])).
% 0.44/0.62  thf('155', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.62  thf('156', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['83', '104'])).
% 0.44/0.62  thf('157', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['113', '134'])).
% 0.44/0.62  thf('158', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 0.44/0.62  thf('159', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['158'])).
% 0.44/0.62  thf('160', plain,
% 0.44/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('161', plain,
% 0.44/0.62      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.62  thf('162', plain,
% 0.44/0.62      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k1_zfmisc_1 @ 
% 0.44/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.62  thf('163', plain,
% 0.44/0.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X32)
% 0.44/0.62          | (v1_xboole_0 @ X33)
% 0.44/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.62          | ~ (v1_funct_1 @ X35)
% 0.44/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.62          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X33)
% 0.44/0.62              = (X35))
% 0.44/0.62          | ~ (m1_subset_1 @ X38 @ 
% 0.44/0.62               (k1_zfmisc_1 @ 
% 0.44/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.62          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.62          | ~ (v1_funct_1 @ X38)
% 0.44/0.62          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.62              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.62                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.62          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.62          | ~ (v1_funct_1 @ X36)
% 0.44/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.62          | (v1_xboole_0 @ X37)
% 0.44/0.62          | (v1_xboole_0 @ X34))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.62  thf('164', plain,
% 0.44/0.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X34)
% 0.44/0.62          | (v1_xboole_0 @ X37)
% 0.44/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.62          | ~ (v1_funct_1 @ X36)
% 0.44/0.62          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.62          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.62              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.62                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.62          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.62          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.62               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.62          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.62               (k1_zfmisc_1 @ 
% 0.44/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.44/0.62              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X33) = (
% 0.44/0.62              X35))
% 0.44/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.62          | ~ (v1_funct_1 @ X35)
% 0.44/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.62          | (v1_xboole_0 @ X33)
% 0.44/0.62          | (v1_xboole_0 @ X32))),
% 0.44/0.62      inference('simplify', [status(thm)], ['163'])).
% 0.44/0.62  thf('165', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.62        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.62        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.62        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['162', '164'])).
% 0.44/0.62  thf('166', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('167', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('168', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('169', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('170', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D)
% 0.44/0.62           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['53', '56'])).
% 0.44/0.62  thf('171', plain,
% 0.44/0.62      (((k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['64', '67'])).
% 0.44/0.62  thf('172', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.62  thf('173', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['83', '104'])).
% 0.44/0.62  thf('174', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D)
% 0.44/0.62           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_D)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['53', '56'])).
% 0.44/0.62  thf('175', plain,
% 0.44/0.62      (((k1_setfam_1 @ (k2_tarski @ sk_C @ sk_D)) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['64', '67'])).
% 0.44/0.62  thf('176', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['110', '111'])).
% 0.44/0.62  thf('177', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['113', '134'])).
% 0.44/0.62  thf('178', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('179', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('180', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('181', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('182', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['165', '166', '167', '168', '169', '170', '171', '172', 
% 0.44/0.62                 '173', '174', '175', '176', '177', '178', '179', '180', '181'])).
% 0.44/0.62  thf('183', plain,
% 0.44/0.62      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['182'])).
% 0.44/0.62  thf('184', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['161', '183'])).
% 0.44/0.62  thf('185', plain,
% 0.44/0.62      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['184'])).
% 0.44/0.62  thf('186', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['160', '185'])).
% 0.44/0.62  thf('187', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['186'])).
% 0.44/0.62  thf('188', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          != (sk_F)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('split', [status(esa)], ['144'])).
% 0.44/0.62  thf('189', plain,
% 0.44/0.62      (((((sk_F) != (sk_F))
% 0.44/0.62         | (v1_xboole_0 @ sk_D)
% 0.44/0.62         | (v1_xboole_0 @ sk_C)
% 0.44/0.62         | (v1_xboole_0 @ sk_B)
% 0.44/0.62         | (v1_xboole_0 @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['187', '188'])).
% 0.44/0.62  thf('190', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_A)
% 0.44/0.62         | (v1_xboole_0 @ sk_B)
% 0.44/0.62         | (v1_xboole_0 @ sk_C)
% 0.44/0.62         | (v1_xboole_0 @ sk_D)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['189'])).
% 0.44/0.62  thf('191', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('192', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['190', '191'])).
% 0.44/0.62  thf('193', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('194', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('clc', [status(thm)], ['192', '193'])).
% 0.44/0.62  thf('195', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('196', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_B))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('clc', [status(thm)], ['194', '195'])).
% 0.44/0.62  thf('197', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('198', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          = (sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['196', '197'])).
% 0.44/0.62  thf('199', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62          = (sk_E))) | 
% 0.44/0.62       ~
% 0.44/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          = (sk_F))) | 
% 0.44/0.62       ~
% 0.44/0.62       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.62      inference('split', [status(esa)], ['144'])).
% 0.44/0.62  thf('200', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62          = (sk_E)))),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['159', '198', '199'])).
% 0.44/0.62  thf('201', plain,
% 0.44/0.62      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62         != (sk_E))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['145', '200'])).
% 0.44/0.62  thf('202', plain,
% 0.44/0.62      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['143', '201'])).
% 0.44/0.62  thf('203', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['15', '202'])).
% 0.44/0.62  thf('204', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['203'])).
% 0.44/0.62  thf('205', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('206', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['204', '205'])).
% 0.44/0.62  thf('207', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('208', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.62      inference('clc', [status(thm)], ['206', '207'])).
% 0.44/0.62  thf('209', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('210', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('clc', [status(thm)], ['208', '209'])).
% 0.44/0.62  thf('211', plain, ($false), inference('demod', [status(thm)], ['0', '210'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
