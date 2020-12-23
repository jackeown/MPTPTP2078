%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aO8tbd0tDs

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:02 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 752 expanded)
%              Number of leaves         :   40 ( 236 expanded)
%              Depth                    :   30
%              Number of atoms          : 3471 (30203 expanded)
%              Number of equality atoms :  112 ( 967 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
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
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
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
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
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
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
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
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
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
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
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
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
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
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
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
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_subset_1 @ X20 @ X21 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
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
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_E @ sk_C_1 ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','77'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X15 ) @ X16 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('88',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('91',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('103',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('106',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['101','102'])).

thf('108',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','88','89','90','95','108','109','110','111','112'])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','114'])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['117'])).

thf('122',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('124',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('128',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('130',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107'])).

thf('131',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['125','126','127','128','129','130'])).

thf('132',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('134',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('136',plain,(
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

thf('137',plain,(
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
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('144',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('146',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('148',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('150',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107'])).

thf('151',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','144','145','146','147','148','149','150','151','152','153','154'])).

thf('156',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['134','156'])).

thf('158',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['133','158'])).

thf('160',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['117'])).

thf('162',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['117'])).

thf('173',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['132','171','172'])).

thf('174',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['118','173'])).

thf('175',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['116','174'])).

thf('176',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['0','183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aO8tbd0tDs
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 216 iterations in 0.154s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.37/0.61  thf(t6_tmap_1, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61               ( ![D:$i]:
% 0.37/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.37/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                   ( ( r1_subset_1 @ C @ D ) =>
% 0.37/0.61                     ( ![E:$i]:
% 0.37/0.61                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.37/0.61                           ( m1_subset_1 @
% 0.37/0.61                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.37/0.61                         ( ![F:$i]:
% 0.37/0.61                           ( ( ( v1_funct_1 @ F ) & 
% 0.37/0.61                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.37/0.61                               ( m1_subset_1 @
% 0.37/0.61                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.37/0.61                             ( ( ( k2_partfun1 @
% 0.37/0.61                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.37/0.61                                 ( k2_partfun1 @
% 0.37/0.61                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.37/0.61                               ( ( k2_partfun1 @
% 0.37/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.37/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.37/0.61                                 ( E ) ) & 
% 0.37/0.61                               ( ( k2_partfun1 @
% 0.37/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.37/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.37/0.61                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61              ( ![C:$i]:
% 0.37/0.61                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                  ( ![D:$i]:
% 0.37/0.61                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.37/0.61                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                      ( ( r1_subset_1 @ C @ D ) =>
% 0.37/0.61                        ( ![E:$i]:
% 0.37/0.61                          ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.61                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.37/0.61                              ( m1_subset_1 @
% 0.37/0.61                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.37/0.61                            ( ![F:$i]:
% 0.37/0.61                              ( ( ( v1_funct_1 @ F ) & 
% 0.37/0.61                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.37/0.61                                  ( m1_subset_1 @
% 0.37/0.61                                    F @ 
% 0.37/0.61                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.37/0.61                                ( ( ( k2_partfun1 @
% 0.37/0.61                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.37/0.61                                    ( k2_partfun1 @
% 0.37/0.61                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.37/0.61                                  ( ( k2_partfun1 @
% 0.37/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.37/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.37/0.61                                    ( E ) ) & 
% 0.37/0.61                                  ( ( k2_partfun1 @
% 0.37/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.37/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.37/0.61                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.37/0.61  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k1_tmap_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ D ) ) & 
% 0.37/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.37/0.61         ( v1_funct_2 @ E @ C @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.37/0.61         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.37/0.61       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.37/0.61         ( v1_funct_2 @
% 0.37/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.37/0.61           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.37/0.61         ( m1_subset_1 @
% 0.37/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.37/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.37/0.61          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.37/0.61          | ~ (v1_funct_1 @ X39)
% 0.37/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.37/0.61          | (v1_xboole_0 @ X42)
% 0.37/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.37/0.61          | (v1_xboole_0 @ X40)
% 0.37/0.61          | (v1_xboole_0 @ X41)
% 0.37/0.61          | (v1_xboole_0 @ X43)
% 0.37/0.61          | ~ (v1_funct_1 @ X44)
% 0.37/0.61          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.37/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.37/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44)))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.37/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ X2)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.37/0.61          | (v1_xboole_0 @ X1)
% 0.37/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.37/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.61  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.37/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ X2)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.37/0.61          | (v1_xboole_0 @ X1)
% 0.37/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.37/0.61      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_D)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.37/0.61          | (v1_funct_1 @ 
% 0.37/0.61             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '8'])).
% 0.37/0.61  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_D)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | (v1_funct_1 @ 
% 0.37/0.61             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.37/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '12'])).
% 0.37/0.61  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_D))),
% 0.37/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.37/0.61          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.37/0.61          | ~ (v1_funct_1 @ X39)
% 0.37/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.37/0.61          | (v1_xboole_0 @ X42)
% 0.37/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.37/0.61          | (v1_xboole_0 @ X40)
% 0.37/0.61          | (v1_xboole_0 @ X41)
% 0.37/0.61          | (v1_xboole_0 @ X43)
% 0.37/0.61          | ~ (v1_funct_1 @ X44)
% 0.37/0.61          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.37/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.37/0.61          | (v1_funct_2 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.37/0.61             (k4_subset_1 @ X43 @ X40 @ X42) @ X41))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.37/0.61           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.37/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.37/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.37/0.61          | ~ (v1_funct_1 @ X2)
% 0.37/0.61          | (v1_xboole_0 @ X1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.61  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.37/0.61           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.37/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.37/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.37/0.61          | ~ (v1_funct_1 @ X2)
% 0.37/0.61          | (v1_xboole_0 @ X1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.37/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_D)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.37/0.61          | (v1_funct_2 @ 
% 0.37/0.61             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['17', '23'])).
% 0.37/0.61  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_D)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | (v1_funct_2 @ 
% 0.37/0.61             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (((v1_funct_2 @ 
% 0.37/0.61         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '27'])).
% 0.37/0.61  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((v1_funct_2 @ 
% 0.37/0.61         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_D))),
% 0.37/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.61  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.37/0.61          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.37/0.61          | ~ (v1_funct_1 @ X39)
% 0.37/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.37/0.61          | (v1_xboole_0 @ X42)
% 0.37/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X43))
% 0.37/0.61          | (v1_xboole_0 @ X40)
% 0.37/0.61          | (v1_xboole_0 @ X41)
% 0.37/0.61          | (v1_xboole_0 @ X43)
% 0.37/0.61          | ~ (v1_funct_1 @ X44)
% 0.37/0.61          | ~ (v1_funct_2 @ X44 @ X42 @ X41)
% 0.37/0.61          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.37/0.61          | (m1_subset_1 @ (k1_tmap_1 @ X43 @ X41 @ X40 @ X42 @ X39 @ X44) @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X43 @ X40 @ X42) @ X41))))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.37/0.61           (k1_zfmisc_1 @ 
% 0.37/0.61            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.37/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.37/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.37/0.61          | ~ (v1_funct_1 @ X2)
% 0.37/0.61          | (v1_xboole_0 @ X1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.61  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.37/0.61           (k1_zfmisc_1 @ 
% 0.37/0.61            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.37/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.37/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.37/0.61          | ~ (v1_funct_1 @ X2)
% 0.37/0.61          | (v1_xboole_0 @ X1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.37/0.61      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_D)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.37/0.61          | (m1_subset_1 @ 
% 0.37/0.61             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '38'])).
% 0.37/0.61  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_D)
% 0.37/0.61          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.61          | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61          | (v1_xboole_0 @ X0)
% 0.37/0.61          | (m1_subset_1 @ 
% 0.37/0.61             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61             (k1_zfmisc_1 @ 
% 0.37/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.37/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (((m1_subset_1 @ 
% 0.37/0.61         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['31', '42'])).
% 0.37/0.61  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (((m1_subset_1 @ 
% 0.37/0.61         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_D))),
% 0.37/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.61  thf(d1_tmap_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61               ( ![D:$i]:
% 0.37/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.37/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                   ( ![E:$i]:
% 0.37/0.61                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.37/0.61                         ( m1_subset_1 @
% 0.37/0.61                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.37/0.61                       ( ![F:$i]:
% 0.37/0.61                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.37/0.61                             ( m1_subset_1 @
% 0.37/0.61                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.37/0.61                           ( ( ( k2_partfun1 @
% 0.37/0.61                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.37/0.61                               ( k2_partfun1 @
% 0.37/0.61                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.37/0.61                             ( ![G:$i]:
% 0.37/0.61                               ( ( ( v1_funct_1 @ G ) & 
% 0.37/0.61                                   ( v1_funct_2 @
% 0.37/0.61                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.37/0.61                                   ( m1_subset_1 @
% 0.37/0.61                                     G @ 
% 0.37/0.61                                     ( k1_zfmisc_1 @
% 0.37/0.61                                       ( k2_zfmisc_1 @
% 0.37/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.37/0.61                                 ( ( ( G ) =
% 0.37/0.61                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.37/0.61                                   ( ( ( k2_partfun1 @
% 0.37/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.37/0.61                                         C ) =
% 0.37/0.61                                       ( E ) ) & 
% 0.37/0.61                                     ( ( k2_partfun1 @
% 0.37/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.37/0.61                                         D ) =
% 0.37/0.61                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X32)
% 0.37/0.61          | (v1_xboole_0 @ X33)
% 0.37/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.37/0.61          | ~ (v1_funct_1 @ X35)
% 0.37/0.61          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.37/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.37/0.61          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.37/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X37)
% 0.37/0.61              = (X36))
% 0.37/0.61          | ~ (m1_subset_1 @ X38 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.37/0.61          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.37/0.61          | ~ (v1_funct_1 @ X38)
% 0.37/0.61          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.37/0.61              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.37/0.61                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.37/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.37/0.61          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.37/0.61          | ~ (v1_funct_1 @ X36)
% 0.37/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.37/0.61          | (v1_xboole_0 @ X37)
% 0.37/0.61          | (v1_xboole_0 @ X34))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X34)
% 0.37/0.61          | (v1_xboole_0 @ X37)
% 0.37/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.37/0.61          | ~ (v1_funct_1 @ X36)
% 0.37/0.61          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.37/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.37/0.61          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.37/0.61              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.37/0.61                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.37/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.37/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.37/0.61               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.37/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.37/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.37/0.61              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X37) = (
% 0.37/0.61              X36))
% 0.37/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.37/0.61          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.37/0.61          | ~ (v1_funct_1 @ X35)
% 0.37/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.37/0.61          | (v1_xboole_0 @ X33)
% 0.37/0.61          | (v1_xboole_0 @ X32))),
% 0.37/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_D)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_D)
% 0.37/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.37/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.37/0.61        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.37/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.61            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.61            = (sk_E))
% 0.37/0.61        | ~ (v1_funct_2 @ 
% 0.37/0.61             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.61             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.61        | ~ (v1_funct_1 @ 
% 0.37/0.61             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.61        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.61            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.61            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.61                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.37/0.61        | ~ (m1_subset_1 @ sk_E @ 
% 0.37/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.37/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.37/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.37/0.61        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['45', '47'])).
% 0.37/0.61  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.37/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.61  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_r1_subset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.37/0.61       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('57', plain,
% 0.37/0.61      (![X20 : $i, X21 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X20)
% 0.37/0.61          | (v1_xboole_0 @ X21)
% 0.37/0.61          | (r1_xboole_0 @ X20 @ X21)
% 0.37/0.61          | ~ (r1_subset_1 @ X20 @ X21))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.37/0.61        | (v1_xboole_0 @ sk_D)
% 0.37/0.61        | (v1_xboole_0 @ sk_C_1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.37/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.37/0.61  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.37/0.61      inference('clc', [status(thm)], ['60', '61'])).
% 0.37/0.61  thf(d7_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.61  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.61  thf('65', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k2_partfun1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.37/0.61          | ~ (v1_funct_1 @ X28)
% 0.37/0.61          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.37/0.61            = (k7_relat_1 @ sk_E @ X0))
% 0.37/0.61          | ~ (v1_funct_1 @ sk_E))),
% 0.37/0.61      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.61  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('69', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.37/0.61           = (k7_relat_1 @ sk_E @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(cc2_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.61  thf('71', plain,
% 0.37/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.61         ((v4_relat_1 @ X25 @ X26)
% 0.37/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.61  thf('72', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 0.37/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.37/0.61  thf(t209_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.61  thf('73', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i]:
% 0.37/0.61         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.37/0.61          | ~ (v4_relat_1 @ X18 @ X19)
% 0.37/0.61          | ~ (v1_relat_1 @ X18))),
% 0.37/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.61  thf('74', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C_1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.37/0.61  thf('75', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(cc1_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( v1_relat_1 @ C ) ))).
% 0.37/0.61  thf('76', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.61         ((v1_relat_1 @ X22)
% 0.37/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.61  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 0.37/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.61  thf('78', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C_1))),
% 0.37/0.61      inference('demod', [status(thm)], ['74', '77'])).
% 0.37/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.61  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.61  thf(t3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.61  thf('80', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i]:
% 0.37/0.61         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.61  thf(d1_xboole_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.61  thf('81', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.61  thf('82', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.61  thf('83', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['79', '82'])).
% 0.37/0.61  thf(t207_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ C ) =>
% 0.37/0.61       ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.61         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.61  thf('84', plain,
% 0.37/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         (~ (r1_xboole_0 @ X15 @ X16)
% 0.37/0.61          | ~ (v1_relat_1 @ X17)
% 0.37/0.61          | ((k7_relat_1 @ (k7_relat_1 @ X17 @ X15) @ X16) = (k1_xboole_0)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.37/0.61  thf('85', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.61          | ~ (v1_relat_1 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.37/0.61  thf('86', plain,
% 0.37/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.61        | ~ (v1_relat_1 @ sk_E))),
% 0.37/0.61      inference('sup+', [status(thm)], ['78', '85'])).
% 0.37/0.61  thf('87', plain, ((v1_relat_1 @ sk_E)),
% 0.37/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.61  thf('88', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.61  thf('89', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.61  thf('90', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.61  thf('91', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('92', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.37/0.61          | ~ (v1_funct_1 @ X28)
% 0.37/0.61          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.37/0.61  thf('93', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.37/0.61          | ~ (v1_funct_1 @ sk_F))),
% 0.37/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.37/0.61  thf('94', plain, ((v1_funct_1 @ sk_F)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('95', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.61  thf('96', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('97', plain,
% 0.37/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.61         ((v4_relat_1 @ X25 @ X26)
% 0.37/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.61  thf('98', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.37/0.61      inference('sup-', [status(thm)], ['96', '97'])).
% 0.37/0.61  thf('99', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i]:
% 0.37/0.61         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.37/0.61          | ~ (v4_relat_1 @ X18 @ X19)
% 0.37/0.61          | ~ (v1_relat_1 @ X18))),
% 0.37/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.61  thf('100', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.61  thf('101', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('102', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.61         ((v1_relat_1 @ X22)
% 0.37/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.62  thf('103', plain, ((v1_relat_1 @ sk_F)),
% 0.37/0.62      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.62  thf('104', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['100', '103'])).
% 0.37/0.62  thf('105', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.62          | ~ (v1_relat_1 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['83', '84'])).
% 0.37/0.62  thf('106', plain,
% 0.37/0.62      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.37/0.62        | ~ (v1_relat_1 @ sk_F))),
% 0.37/0.62      inference('sup+', [status(thm)], ['104', '105'])).
% 0.37/0.62  thf('107', plain, ((v1_relat_1 @ sk_F)),
% 0.37/0.62      inference('sup-', [status(thm)], ['101', '102'])).
% 0.37/0.62  thf('108', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.37/0.62  thf('109', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('110', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('112', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('113', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62            = (sk_E))
% 0.37/0.62        | ~ (v1_funct_2 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.62        | ~ (v1_funct_1 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['48', '49', '50', '51', '52', '55', '64', '69', '88', '89', 
% 0.37/0.62                 '90', '95', '108', '109', '110', '111', '112'])).
% 0.37/0.62  thf('114', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ 
% 0.37/0.62           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ~ (v1_funct_2 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62            = (sk_E))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify', [status(thm)], ['113'])).
% 0.37/0.62  thf('115', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62            = (sk_E))
% 0.37/0.62        | ~ (v1_funct_1 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['30', '114'])).
% 0.37/0.62  thf('116', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ 
% 0.37/0.62           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62            = (sk_E))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify', [status(thm)], ['115'])).
% 0.37/0.62  thf('117', plain,
% 0.37/0.62      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62            != (sk_E))
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            != (sk_F)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('118', plain,
% 0.37/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62          != (sk_E)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_C_1) = (sk_E))))),
% 0.37/0.62      inference('split', [status(esa)], ['117'])).
% 0.37/0.62  thf('119', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.62  thf('120', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.62  thf('121', plain,
% 0.37/0.62      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.37/0.62      inference('split', [status(esa)], ['117'])).
% 0.37/0.62  thf('122', plain,
% 0.37/0.62      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['120', '121'])).
% 0.37/0.62  thf('123', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.62  thf('124', plain,
% 0.37/0.62      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 0.37/0.62          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.37/0.62      inference('demod', [status(thm)], ['122', '123'])).
% 0.37/0.62  thf('125', plain,
% 0.37/0.62      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 0.37/0.62          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['119', '124'])).
% 0.37/0.62  thf('126', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('127', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.37/0.62           = (k7_relat_1 @ sk_E @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['67', '68'])).
% 0.37/0.62  thf('128', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.62  thf('129', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('130', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.37/0.62  thf('131', plain,
% 0.37/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['125', '126', '127', '128', '129', '130'])).
% 0.37/0.62  thf('132', plain,
% 0.37/0.62      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['131'])).
% 0.37/0.62  thf('133', plain,
% 0.37/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.62  thf('134', plain,
% 0.37/0.62      (((v1_funct_2 @ 
% 0.37/0.62         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.62  thf('135', plain,
% 0.37/0.62      (((m1_subset_1 @ 
% 0.37/0.62         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62         (k1_zfmisc_1 @ 
% 0.37/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.62  thf('136', plain,
% 0.37/0.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ X32)
% 0.37/0.62          | (v1_xboole_0 @ X33)
% 0.37/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.37/0.62          | ~ (v1_funct_1 @ X35)
% 0.37/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.37/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.37/0.62          | ((X38) != (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.37/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ X38 @ X33)
% 0.37/0.62              = (X35))
% 0.37/0.62          | ~ (m1_subset_1 @ X38 @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.37/0.62          | ~ (v1_funct_2 @ X38 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.37/0.62          | ~ (v1_funct_1 @ X38)
% 0.37/0.62          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.37/0.62              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.37/0.62                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.37/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.37/0.62          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.37/0.62          | ~ (v1_funct_1 @ X36)
% 0.37/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.37/0.62          | (v1_xboole_0 @ X37)
% 0.37/0.62          | (v1_xboole_0 @ X34))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.37/0.62  thf('137', plain,
% 0.37/0.62      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ X34)
% 0.37/0.62          | (v1_xboole_0 @ X37)
% 0.37/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X34))
% 0.37/0.62          | ~ (v1_funct_1 @ X36)
% 0.37/0.62          | ~ (v1_funct_2 @ X36 @ X37 @ X32)
% 0.37/0.62          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X32)))
% 0.37/0.62          | ((k2_partfun1 @ X37 @ X32 @ X36 @ (k9_subset_1 @ X34 @ X37 @ X33))
% 0.37/0.62              != (k2_partfun1 @ X33 @ X32 @ X35 @ 
% 0.37/0.62                  (k9_subset_1 @ X34 @ X37 @ X33)))
% 0.37/0.62          | ~ (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35))
% 0.37/0.62          | ~ (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.37/0.62               (k4_subset_1 @ X34 @ X37 @ X33) @ X32)
% 0.37/0.62          | ~ (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32)))
% 0.37/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X34 @ X37 @ X33) @ X32 @ 
% 0.37/0.62              (k1_tmap_1 @ X34 @ X32 @ X37 @ X33 @ X36 @ X35) @ X33) = (
% 0.37/0.62              X35))
% 0.37/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.37/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.37/0.62          | ~ (v1_funct_1 @ X35)
% 0.37/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.37/0.62          | (v1_xboole_0 @ X33)
% 0.37/0.62          | (v1_xboole_0 @ X32))),
% 0.37/0.62      inference('simplify', [status(thm)], ['136'])).
% 0.37/0.62  thf('138', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.37/0.62        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.37/0.62        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            = (sk_F))
% 0.37/0.62        | ~ (v1_funct_2 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.62        | ~ (v1_funct_1 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.37/0.62        | ~ (m1_subset_1 @ sk_E @ 
% 0.37/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.37/0.62        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.37/0.62        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['135', '137'])).
% 0.37/0.62  thf('139', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('140', plain, ((v1_funct_1 @ sk_F)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('141', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('142', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('143', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.62  thf('144', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('145', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.37/0.62           = (k7_relat_1 @ sk_E @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['67', '68'])).
% 0.37/0.62  thf('146', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.62  thf('147', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.62  thf('148', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.62  thf('149', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.62  thf('150', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.62      inference('demod', [status(thm)], ['106', '107'])).
% 0.37/0.62  thf('151', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('152', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('153', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('154', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('155', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            = (sk_F))
% 0.37/0.62        | ~ (v1_funct_2 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.62        | ~ (v1_funct_1 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)],
% 0.37/0.62                ['138', '139', '140', '141', '142', '143', '144', '145', 
% 0.37/0.62                 '146', '147', '148', '149', '150', '151', '152', '153', '154'])).
% 0.37/0.62  thf('156', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ 
% 0.37/0.62           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ~ (v1_funct_2 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            = (sk_F))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify', [status(thm)], ['155'])).
% 0.37/0.62  thf('157', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            = (sk_F))
% 0.37/0.62        | ~ (v1_funct_1 @ 
% 0.37/0.62             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['134', '156'])).
% 0.37/0.62  thf('158', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ 
% 0.37/0.62           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            = (sk_F))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify', [status(thm)], ['157'])).
% 0.37/0.62  thf('159', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62            = (sk_F)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['133', '158'])).
% 0.37/0.62  thf('160', plain,
% 0.37/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62          = (sk_F))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify', [status(thm)], ['159'])).
% 0.37/0.62  thf('161', plain,
% 0.37/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62          != (sk_F)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_D) = (sk_F))))),
% 0.37/0.62      inference('split', [status(esa)], ['117'])).
% 0.37/0.62  thf('162', plain,
% 0.37/0.62      (((((sk_F) != (sk_F))
% 0.37/0.62         | (v1_xboole_0 @ sk_D)
% 0.37/0.62         | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62         | (v1_xboole_0 @ sk_A)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_D) = (sk_F))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['160', '161'])).
% 0.37/0.62  thf('163', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62         | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62         | (v1_xboole_0 @ sk_D)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_D) = (sk_F))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['162'])).
% 0.37/0.62  thf('164', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('165', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_D) = (sk_F))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['163', '164'])).
% 0.37/0.62  thf('166', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('167', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_D) = (sk_F))))),
% 0.37/0.62      inference('clc', [status(thm)], ['165', '166'])).
% 0.37/0.62  thf('168', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('169', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_B_1))
% 0.37/0.62         <= (~
% 0.37/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.37/0.62                sk_D) = (sk_F))))),
% 0.37/0.62      inference('clc', [status(thm)], ['167', '168'])).
% 0.37/0.62  thf('170', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('171', plain,
% 0.37/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62          = (sk_F)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['169', '170'])).
% 0.37/0.62  thf('172', plain,
% 0.37/0.62      (~
% 0.37/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62          = (sk_E))) | 
% 0.37/0.62       ~
% 0.37/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.37/0.62          = (sk_F))) | 
% 0.37/0.62       ~
% 0.37/0.62       (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.37/0.62          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.37/0.62          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.37/0.62             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.37/0.62      inference('split', [status(esa)], ['117'])).
% 0.37/0.62  thf('173', plain,
% 0.37/0.62      (~
% 0.37/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62          = (sk_E)))),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['132', '171', '172'])).
% 0.37/0.62  thf('174', plain,
% 0.37/0.62      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.37/0.62         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.37/0.62         != (sk_E))),
% 0.37/0.62      inference('simpl_trail', [status(thm)], ['118', '173'])).
% 0.37/0.62  thf('175', plain,
% 0.37/0.62      ((~ (v1_funct_1 @ 
% 0.37/0.62           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify_reflect-', [status(thm)], ['116', '174'])).
% 0.37/0.62  thf('176', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_D)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['15', '175'])).
% 0.37/0.62  thf('177', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_C_1)
% 0.37/0.62        | (v1_xboole_0 @ sk_D))),
% 0.37/0.62      inference('simplify', [status(thm)], ['176'])).
% 0.37/0.62  thf('178', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('179', plain,
% 0.37/0.62      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['177', '178'])).
% 0.37/0.62  thf('180', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('181', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.37/0.62      inference('clc', [status(thm)], ['179', '180'])).
% 0.37/0.62  thf('182', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('183', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.37/0.62      inference('clc', [status(thm)], ['181', '182'])).
% 0.37/0.62  thf('184', plain, ($false), inference('demod', [status(thm)], ['0', '183'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
