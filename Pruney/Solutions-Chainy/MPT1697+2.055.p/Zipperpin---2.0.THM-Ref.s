%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6NHgPMViDu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:01 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  248 ( 857 expanded)
%              Number of leaves         :   44 ( 269 expanded)
%              Depth                    :   31
%              Number of atoms          : 3613 (35097 expanded)
%              Number of equality atoms :  113 (1111 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_subset_1 @ X13 @ X14 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_partfun1 @ sk_E @ sk_C_1 ),
    inference(clc,[status(thm)],['80','81'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('86',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('89',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v4_relat_1 @ sk_E @ sk_C_1 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C_1 ),
    inference(demod,[status(thm)],['84','87','90'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['85','86'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('99',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('105',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('117',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('120',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['114','117','120'])).

thf('122',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['115','116'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','96','97','98','103','126','127','128','129','130'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
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
    inference('sup-',[status(thm)],['30','132'])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('139',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['135'])).

thf('140',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('142',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('143',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('144',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('147',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','95'])).

thf('148',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','125'])).

thf('149',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('152',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('153',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('154',plain,(
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

thf('155',plain,(
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
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
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
    inference('sup-',[status(thm)],['153','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('162',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('164',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','95'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('166',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('168',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','125'])).

thf('169',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
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
    inference(demod,[status(thm)],['156','157','158','159','160','161','162','163','164','165','166','167','168','169','170','171','172'])).

thf('174',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
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
    inference('sup-',[status(thm)],['152','174'])).

thf('176',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
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
    inference('sup-',[status(thm)],['151','176'])).

thf('178',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['135'])).

thf('180',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['135'])).

thf('191',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['150','189','190'])).

thf('192',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['136','191'])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['134','192'])).

thf('194',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','193'])).

thf('195',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    $false ),
    inference(demod,[status(thm)],['0','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6NHgPMViDu
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:29:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 195 iterations in 0.177s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.64  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.64  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.64  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.64  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.64  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.64  thf(t6_tmap_1, conjecture,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.64           ( ![C:$i]:
% 0.44/0.64             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.64               ( ![D:$i]:
% 0.44/0.64                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.64                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.64                   ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.64                     ( ![E:$i]:
% 0.44/0.64                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.64                           ( m1_subset_1 @
% 0.44/0.64                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.64                         ( ![F:$i]:
% 0.44/0.64                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.64                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.64                               ( m1_subset_1 @
% 0.44/0.64                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.64                             ( ( ( k2_partfun1 @
% 0.44/0.64                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.64                                 ( k2_partfun1 @
% 0.44/0.64                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.64                               ( ( k2_partfun1 @
% 0.44/0.64                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.64                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.64                                 ( E ) ) & 
% 0.44/0.64                               ( ( k2_partfun1 @
% 0.44/0.64                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.64                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.64                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i]:
% 0.44/0.64        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64          ( ![B:$i]:
% 0.44/0.64            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.64              ( ![C:$i]:
% 0.44/0.64                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.64                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.64                  ( ![D:$i]:
% 0.44/0.64                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.64                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.64                      ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.64                        ( ![E:$i]:
% 0.44/0.64                          ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.64                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.64                              ( m1_subset_1 @
% 0.44/0.64                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.64                            ( ![F:$i]:
% 0.44/0.64                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.64                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.64                                  ( m1_subset_1 @
% 0.44/0.64                                    F @ 
% 0.44/0.64                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.64                                ( ( ( k2_partfun1 @
% 0.44/0.64                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.64                                    ( k2_partfun1 @
% 0.44/0.64                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.64                                  ( ( k2_partfun1 @
% 0.44/0.64                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.64                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.64                                    ( E ) ) & 
% 0.44/0.64                                  ( ( k2_partfun1 @
% 0.44/0.64                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.64                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.64                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.44/0.64  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(dt_k1_tmap_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.64         ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.64         ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.44/0.64         ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.44/0.64         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.64       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.64         ( v1_funct_2 @
% 0.44/0.64           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.64           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.64         ( m1_subset_1 @
% 0.44/0.64           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.44/0.64          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.44/0.64          | ~ (v1_funct_1 @ X39)
% 0.44/0.64          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.44/0.64          | (v1_xboole_0 @ X42)
% 0.44/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.44/0.64          | (v1_xboole_0 @ X40)
% 0.44/0.64          | (v1_xboole_0 @ X41)
% 0.44/0.64          | (v1_xboole_0 @ X43)
% 0.44/0.64          | ~ (v1_funct_1 @ X44)
% 0.44/0.64          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.44/0.64          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.44/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44)))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | (v1_xboole_0 @ X2)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.64          | (v1_xboole_0 @ X1)
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.64  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('8', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | (v1_xboole_0 @ X2)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.64          | (v1_xboole_0 @ X1)
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.64      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_D)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.64  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('12', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_D)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.64      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['1', '12'])).
% 0.44/0.64  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('15', plain,
% 0.44/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | (v1_xboole_0 @ sk_D))),
% 0.44/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.64  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('17', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.44/0.64          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.44/0.64          | ~ (v1_funct_1 @ X39)
% 0.44/0.64          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.44/0.64          | (v1_xboole_0 @ X42)
% 0.44/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.44/0.64          | (v1_xboole_0 @ X40)
% 0.44/0.64          | (v1_xboole_0 @ X41)
% 0.44/0.64          | (v1_xboole_0 @ X43)
% 0.44/0.64          | ~ (v1_funct_1 @ X44)
% 0.44/0.64          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.44/0.64          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.44/0.64          | (v1_funct_2 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.44/0.64             (k4_subset_1 @ X43 @ X40 @ X42) @ X41))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.64  thf('20', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.64           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.64          | ~ (v1_funct_1 @ X2)
% 0.44/0.64          | (v1_xboole_0 @ X1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.64  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('23', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.64           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.64          | ~ (v1_funct_1 @ X2)
% 0.44/0.64          | (v1_xboole_0 @ X1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.64      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.64  thf('24', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_D)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.64          | (v1_funct_2 @ 
% 0.44/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['17', '23'])).
% 0.44/0.64  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('27', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_D)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | (v1_funct_2 @ 
% 0.44/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.64  thf('28', plain,
% 0.44/0.64      (((v1_funct_2 @ 
% 0.44/0.64         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['16', '27'])).
% 0.44/0.64  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('30', plain,
% 0.44/0.64      (((v1_funct_2 @ 
% 0.44/0.64         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | (v1_xboole_0 @ sk_D))),
% 0.44/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.64  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('32', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.44/0.64          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.44/0.64          | ~ (v1_funct_1 @ X39)
% 0.44/0.64          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.44/0.64          | (v1_xboole_0 @ X42)
% 0.44/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.44/0.64          | (v1_xboole_0 @ X40)
% 0.44/0.64          | (v1_xboole_0 @ X41)
% 0.44/0.64          | (v1_xboole_0 @ X43)
% 0.44/0.64          | ~ (v1_funct_1 @ X44)
% 0.44/0.64          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.44/0.64          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.44/0.64          | (m1_subset_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.44/0.64             (k1_zfmisc_1 @ 
% 0.44/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X43 @ X40 @ X42) @ X41))))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.64  thf('35', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.64           (k1_zfmisc_1 @ 
% 0.44/0.64            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.64          | ~ (v1_funct_1 @ X2)
% 0.44/0.64          | (v1_xboole_0 @ X1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.64  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('38', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.44/0.64           (k1_zfmisc_1 @ 
% 0.44/0.64            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.44/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.64          | ~ (v1_funct_1 @ X2)
% 0.44/0.64          | (v1_xboole_0 @ X1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.64      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.44/0.64  thf('39', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_D)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.64          | (m1_subset_1 @ 
% 0.44/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64             (k1_zfmisc_1 @ 
% 0.44/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['32', '38'])).
% 0.44/0.64  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('42', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_D)
% 0.44/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.44/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64          | (v1_xboole_0 @ sk_B)
% 0.44/0.64          | (v1_xboole_0 @ X0)
% 0.44/0.64          | (m1_subset_1 @ 
% 0.44/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64             (k1_zfmisc_1 @ 
% 0.44/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 0.44/0.64      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.64  thf('43', plain,
% 0.44/0.64      (((m1_subset_1 @ 
% 0.44/0.64         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64         (k1_zfmisc_1 @ 
% 0.44/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['31', '42'])).
% 0.44/0.64  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('45', plain,
% 0.44/0.64      (((m1_subset_1 @ 
% 0.44/0.64         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64         (k1_zfmisc_1 @ 
% 0.44/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | (v1_xboole_0 @ sk_D))),
% 0.44/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.64  thf(d1_tmap_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.64           ( ![C:$i]:
% 0.44/0.64             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.64               ( ![D:$i]:
% 0.44/0.64                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.64                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.64                   ( ![E:$i]:
% 0.44/0.64                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.64                         ( m1_subset_1 @
% 0.44/0.64                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.64                       ( ![F:$i]:
% 0.44/0.64                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.64                             ( m1_subset_1 @
% 0.44/0.64                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.64                           ( ( ( k2_partfun1 @
% 0.44/0.64                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.64                               ( k2_partfun1 @
% 0.44/0.64                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.44/0.64                             ( ![G:$i]:
% 0.44/0.64                               ( ( ( v1_funct_1 @ G ) & 
% 0.44/0.64                                   ( v1_funct_2 @
% 0.44/0.64                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.64                                   ( m1_subset_1 @
% 0.44/0.64                                     G @ 
% 0.44/0.64                                     ( k1_zfmisc_1 @
% 0.44/0.64                                       ( k2_zfmisc_1 @
% 0.44/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.44/0.64                                 ( ( ( G ) =
% 0.44/0.64                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.64                                   ( ( ( k2_partfun1 @
% 0.44/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.64                                         C ) =
% 0.44/0.64                                       ( E ) ) & 
% 0.44/0.64                                     ( ( k2_partfun1 @
% 0.44/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.64                                         D ) =
% 0.44/0.64                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.64  thf('46', plain,
% 0.44/0.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.64         ((v1_xboole_0 @ X32)
% 0.44/0.64          | (v1_xboole_0 @ X33)
% 0.44/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.64          | ~ (v1_funct_1 @ X35)
% 0.44/0.64          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.64          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X37)
% 0.44/0.64              = (X36))
% 0.44/0.64          | ~ (m1_subset_1 @ X38 @ 
% 0.44/0.64               (k1_zfmisc_1 @ 
% 0.44/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.64          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.64          | ~ (v1_funct_1 @ X38)
% 0.44/0.64          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.64              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.64                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.64          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.64          | ~ (v1_funct_1 @ X36)
% 0.44/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.64          | (v1_xboole_0 @ X37)
% 0.44/0.64          | (v1_xboole_0 @ X34))),
% 0.44/0.64      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.64  thf('47', plain,
% 0.44/0.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.64         ((v1_xboole_0 @ X34)
% 0.44/0.64          | (v1_xboole_0 @ X37)
% 0.44/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.64          | ~ (v1_funct_1 @ X36)
% 0.44/0.64          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.64          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.64              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.64                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.64          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.64          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.64               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.64          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.64               (k1_zfmisc_1 @ 
% 0.44/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.44/0.64              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X37) = (
% 0.44/0.64              X36))
% 0.44/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.64          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.64          | ~ (v1_funct_1 @ X35)
% 0.44/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.64          | (v1_xboole_0 @ X33)
% 0.44/0.64          | (v1_xboole_0 @ X32))),
% 0.44/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.64  thf('48', plain,
% 0.44/0.64      (((v1_xboole_0 @ sk_D)
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_A)
% 0.44/0.64        | (v1_xboole_0 @ sk_B)
% 0.44/0.64        | (v1_xboole_0 @ sk_D)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.64            = (sk_E))
% 0.44/0.64        | ~ (v1_funct_2 @ 
% 0.44/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.64             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.64        | ~ (v1_funct_1 @ 
% 0.44/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.64        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.64            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.64            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.44/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.44/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.64        | (v1_xboole_0 @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['45', '47'])).
% 0.44/0.64  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('52', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.64       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.64  thf('54', plain,
% 0.44/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.64         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.44/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.64  thf('55', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.65       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.65  thf('57', plain,
% 0.44/0.65      (![X13 : $i, X14 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X13)
% 0.44/0.65          | (v1_xboole_0 @ X14)
% 0.44/0.65          | (r1_xboole_0 @ X13 @ X14)
% 0.44/0.65          | ~ (r1_subset_1 @ X13 @ X14))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.65  thf('58', plain,
% 0.44/0.65      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.65  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.44/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.44/0.65  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.44/0.65      inference('clc', [status(thm)], ['60', '61'])).
% 0.44/0.65  thf(d7_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.65  thf('63', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.65  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('65', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.65  thf('66', plain,
% 0.44/0.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.44/0.65          | ~ (v1_funct_1 @ X28)
% 0.44/0.65          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.65  thf('67', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.65  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('69', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.65  thf('70', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.44/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.65  thf(t3_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.44/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.44/0.65  thf('71', plain,
% 0.44/0.65      (![X3 : $i, X4 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.44/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.44/0.65  thf(t7_ordinal1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.65  thf('72', plain,
% 0.44/0.65      (![X15 : $i, X16 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.44/0.65  thf('73', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.65  thf('74', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['70', '73'])).
% 0.44/0.65  thf('75', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc5_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.65       ( ![C:$i]:
% 0.44/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.65             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.65  thf('76', plain,
% 0.44/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.44/0.65          | (v1_partfun1 @ X23 @ X24)
% 0.44/0.65          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.44/0.65          | ~ (v1_funct_1 @ X23)
% 0.44/0.65          | (v1_xboole_0 @ X25))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.65  thf('77', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.44/0.65        | (v1_partfun1 @ sk_E @ sk_C_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.44/0.65  thf('78', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('79', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('80', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C_1))),
% 0.44/0.65      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.44/0.65  thf('81', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('82', plain, ((v1_partfun1 @ sk_E @ sk_C_1)),
% 0.44/0.65      inference('clc', [status(thm)], ['80', '81'])).
% 0.44/0.65  thf(d4_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.65  thf('83', plain,
% 0.44/0.65      (![X26 : $i, X27 : $i]:
% 0.44/0.65         (~ (v1_partfun1 @ X27 @ X26)
% 0.44/0.65          | ((k1_relat_1 @ X27) = (X26))
% 0.44/0.65          | ~ (v4_relat_1 @ X27 @ X26)
% 0.44/0.65          | ~ (v1_relat_1 @ X27))),
% 0.44/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.65  thf('84', plain,
% 0.44/0.65      ((~ (v1_relat_1 @ sk_E)
% 0.44/0.65        | ~ (v4_relat_1 @ sk_E @ sk_C_1)
% 0.44/0.65        | ((k1_relat_1 @ sk_E) = (sk_C_1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['82', '83'])).
% 0.44/0.65  thf('85', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc1_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( v1_relat_1 @ C ) ))).
% 0.44/0.65  thf('86', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X17)
% 0.44/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('87', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.65      inference('sup-', [status(thm)], ['85', '86'])).
% 0.44/0.65  thf('88', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.65  thf('89', plain,
% 0.44/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X20 @ X21)
% 0.44/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('90', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 0.44/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.44/0.65  thf('91', plain, (((k1_relat_1 @ sk_E) = (sk_C_1))),
% 0.44/0.65      inference('demod', [status(thm)], ['84', '87', '90'])).
% 0.44/0.65  thf(t187_relat_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ A ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.65           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.65  thf('92', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.65          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.65  thf('93', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 0.44/0.65          | ~ (v1_relat_1 @ sk_E)
% 0.44/0.65          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.65  thf('94', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.65      inference('sup-', [status(thm)], ['85', '86'])).
% 0.44/0.65  thf('95', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 0.44/0.65          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['93', '94'])).
% 0.44/0.65  thf('96', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['74', '95'])).
% 0.44/0.65  thf('97', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('98', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('99', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('100', plain,
% 0.44/0.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.44/0.65          | ~ (v1_funct_1 @ X28)
% 0.44/0.65          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.65  thf('101', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.65      inference('sup-', [status(thm)], ['99', '100'])).
% 0.44/0.65  thf('102', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('103', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['101', '102'])).
% 0.44/0.65  thf('104', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['70', '73'])).
% 0.44/0.65  thf('105', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('106', plain,
% 0.44/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.44/0.65          | (v1_partfun1 @ X23 @ X24)
% 0.44/0.65          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.44/0.65          | ~ (v1_funct_1 @ X23)
% 0.44/0.65          | (v1_xboole_0 @ X25))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.65  thf('107', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.65  thf('108', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('109', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('110', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.44/0.65  thf('111', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('112', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.44/0.65      inference('clc', [status(thm)], ['110', '111'])).
% 0.44/0.65  thf('113', plain,
% 0.44/0.65      (![X26 : $i, X27 : $i]:
% 0.44/0.65         (~ (v1_partfun1 @ X27 @ X26)
% 0.44/0.65          | ((k1_relat_1 @ X27) = (X26))
% 0.44/0.65          | ~ (v4_relat_1 @ X27 @ X26)
% 0.44/0.65          | ~ (v1_relat_1 @ X27))),
% 0.44/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.65  thf('114', plain,
% 0.44/0.65      ((~ (v1_relat_1 @ sk_F)
% 0.44/0.65        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.44/0.65        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['112', '113'])).
% 0.44/0.65  thf('115', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('116', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X17)
% 0.44/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('117', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.65      inference('sup-', [status(thm)], ['115', '116'])).
% 0.44/0.65  thf('118', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('119', plain,
% 0.44/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X20 @ X21)
% 0.44/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('120', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['118', '119'])).
% 0.44/0.65  thf('121', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['114', '117', '120'])).
% 0.44/0.65  thf('122', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.65          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.65  thf('123', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.65          | ~ (v1_relat_1 @ sk_F)
% 0.44/0.65          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['121', '122'])).
% 0.44/0.65  thf('124', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.65      inference('sup-', [status(thm)], ['115', '116'])).
% 0.44/0.65  thf('125', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.65          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['123', '124'])).
% 0.44/0.65  thf('126', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['104', '125'])).
% 0.44/0.65  thf('127', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('128', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('130', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('131', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['48', '49', '50', '51', '52', '55', '64', '69', '96', '97', 
% 0.44/0.65                 '98', '103', '126', '127', '128', '129', '130'])).
% 0.44/0.65  thf('132', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['131'])).
% 0.44/0.65  thf('133', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | ~ (v1_funct_1 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '132'])).
% 0.44/0.65  thf('134', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['133'])).
% 0.44/0.65  thf('135', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65            != (sk_E))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            != (sk_F)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('136', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65          != (sk_E)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65                sk_C_1) = (sk_E))))),
% 0.44/0.65      inference('split', [status(esa)], ['135'])).
% 0.44/0.65  thf('137', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['101', '102'])).
% 0.44/0.65  thf('138', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('139', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.65      inference('split', [status(esa)], ['135'])).
% 0.44/0.65  thf('140', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['138', '139'])).
% 0.44/0.65  thf('141', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('142', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('143', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('144', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.65      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.44/0.65  thf('145', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.65          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['137', '144'])).
% 0.44/0.65  thf('146', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.65  thf('147', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['74', '95'])).
% 0.44/0.65  thf('148', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['104', '125'])).
% 0.44/0.65  thf('149', plain,
% 0.44/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.44/0.65      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.44/0.65  thf('150', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['149'])).
% 0.44/0.65  thf('151', plain,
% 0.44/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.65  thf('152', plain,
% 0.44/0.65      (((v1_funct_2 @ 
% 0.44/0.65         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.65  thf('153', plain,
% 0.44/0.65      (((m1_subset_1 @ 
% 0.44/0.65         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k1_zfmisc_1 @ 
% 0.44/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.65  thf('154', plain,
% 0.44/0.65      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X32)
% 0.44/0.65          | (v1_xboole_0 @ X33)
% 0.44/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.65          | ~ (v1_funct_1 @ X35)
% 0.44/0.65          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.65          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X33)
% 0.44/0.65              = (X35))
% 0.44/0.65          | ~ (m1_subset_1 @ X38 @ 
% 0.44/0.65               (k1_zfmisc_1 @ 
% 0.44/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.65          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.65          | ~ (v1_funct_1 @ X38)
% 0.44/0.65          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.65              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.65                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.65          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.65          | ~ (v1_funct_1 @ X36)
% 0.44/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.65          | (v1_xboole_0 @ X37)
% 0.44/0.65          | (v1_xboole_0 @ X34))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.65  thf('155', plain,
% 0.44/0.65      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X34)
% 0.44/0.65          | (v1_xboole_0 @ X37)
% 0.44/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.44/0.65          | ~ (v1_funct_1 @ X36)
% 0.44/0.65          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.44/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.44/0.65          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.44/0.65              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.44/0.65                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.44/0.65          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.44/0.65          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.65               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.44/0.65          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.44/0.65               (k1_zfmisc_1 @ 
% 0.44/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.44/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.44/0.65              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X33) = (
% 0.44/0.65              X35))
% 0.44/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.44/0.65          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.44/0.65          | ~ (v1_funct_1 @ X35)
% 0.44/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.44/0.65          | (v1_xboole_0 @ X33)
% 0.44/0.65          | (v1_xboole_0 @ X32))),
% 0.44/0.65      inference('simplify', [status(thm)], ['154'])).
% 0.44/0.65  thf('156', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.44/0.65        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.44/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['153', '155'])).
% 0.44/0.65  thf('157', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('158', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('159', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('160', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('161', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('162', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('163', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.65  thf('164', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['74', '95'])).
% 0.44/0.65  thf('165', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('166', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.65  thf('167', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['101', '102'])).
% 0.44/0.65  thf('168', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['104', '125'])).
% 0.44/0.65  thf('169', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('170', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('171', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('172', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('173', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['156', '157', '158', '159', '160', '161', '162', '163', 
% 0.44/0.65                 '164', '165', '166', '167', '168', '169', '170', '171', '172'])).
% 0.44/0.65  thf('174', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['173'])).
% 0.44/0.65  thf('175', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | ~ (v1_funct_1 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['152', '174'])).
% 0.44/0.65  thf('176', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['175'])).
% 0.44/0.65  thf('177', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['151', '176'])).
% 0.44/0.65  thf('178', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          = (sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['177'])).
% 0.44/0.65  thf('179', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          != (sk_F)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('split', [status(esa)], ['135'])).
% 0.44/0.65  thf('180', plain,
% 0.44/0.65      (((((sk_F) != (sk_F))
% 0.44/0.65         | (v1_xboole_0 @ sk_D)
% 0.44/0.65         | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65         | (v1_xboole_0 @ sk_B)
% 0.44/0.65         | (v1_xboole_0 @ sk_A)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['178', '179'])).
% 0.44/0.65  thf('181', plain,
% 0.44/0.65      ((((v1_xboole_0 @ sk_A)
% 0.44/0.65         | (v1_xboole_0 @ sk_B)
% 0.44/0.65         | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65         | (v1_xboole_0 @ sk_D)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['180'])).
% 0.44/0.65  thf('182', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('183', plain,
% 0.44/0.65      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['181', '182'])).
% 0.44/0.65  thf('184', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('185', plain,
% 0.44/0.65      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('clc', [status(thm)], ['183', '184'])).
% 0.44/0.65  thf('186', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('187', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('clc', [status(thm)], ['185', '186'])).
% 0.44/0.65  thf('188', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('189', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          = (sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['187', '188'])).
% 0.44/0.65  thf('190', plain,
% 0.44/0.65      (~
% 0.44/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65          = (sk_E))) | 
% 0.44/0.65       ~
% 0.44/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          = (sk_F))) | 
% 0.44/0.65       ~
% 0.44/0.65       (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.44/0.65          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.44/0.65          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.44/0.65      inference('split', [status(esa)], ['135'])).
% 0.44/0.65  thf('191', plain,
% 0.44/0.65      (~
% 0.44/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65          = (sk_E)))),
% 0.44/0.65      inference('sat_resolution*', [status(thm)], ['150', '189', '190'])).
% 0.44/0.65  thf('192', plain,
% 0.44/0.65      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.44/0.65         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.44/0.65         != (sk_E))),
% 0.44/0.65      inference('simpl_trail', [status(thm)], ['136', '191'])).
% 0.44/0.65  thf('193', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['134', '192'])).
% 0.44/0.65  thf('194', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['15', '193'])).
% 0.44/0.65  thf('195', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['194'])).
% 0.44/0.65  thf('196', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('197', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['195', '196'])).
% 0.44/0.65  thf('198', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('199', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('clc', [status(thm)], ['197', '198'])).
% 0.44/0.65  thf('200', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('201', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('clc', [status(thm)], ['199', '200'])).
% 0.44/0.65  thf('202', plain, ($false), inference('demod', [status(thm)], ['0', '201'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
