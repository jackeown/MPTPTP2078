%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ef1YV3lhnw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:06 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 788 expanded)
%              Number of leaves         :   41 ( 248 expanded)
%              Depth                    :   30
%              Number of atoms          : 3487 (30363 expanded)
%              Number of equality atoms :  112 ( 967 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47 ) ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47 ) @ ( k4_subset_1 @ X46 @ X43 @ X45 ) @ X44 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X46 @ X43 @ X45 ) @ X44 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ( X41
       != ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ X41 @ X40 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ X40 )
        = X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_subset_1 @ X26 @ X27 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
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

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('86',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X23 @ X21 ) @ X22 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['77','78'])).

thf('90',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('100',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_F ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('110',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_F ),
    inference(demod,[status(thm)],['105','106'])).

thf('112',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','90','91','92','97','112','113','114','115','116'])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
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
    inference('sup-',[status(thm)],['30','118'])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('125',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['121'])).

thf('126',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('130',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['123','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('133',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('134',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','111'])).

thf('135',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('138',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('140',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ( X41
       != ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ X41 @ X36 )
        = X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('141',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ X36 )
        = X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
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
    inference('sup-',[status(thm)],['139','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('150',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('152',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('154',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['110','111'])).

thf('155',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
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
    inference(demod,[status(thm)],['142','143','144','145','146','147','148','149','150','151','152','153','154','155','156','157','158'])).

thf('160',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
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
    inference('sup-',[status(thm)],['138','160'])).

thf('162',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
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
    inference('sup-',[status(thm)],['137','162'])).

thf('164',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['121'])).

thf('166',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['121'])).

thf('177',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['136','175','176'])).

thf('178',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['122','177'])).

thf('179',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['120','178'])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    $false ),
    inference(demod,[status(thm)],['0','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ef1YV3lhnw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 224 iterations in 0.229s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.48/0.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.69  thf(sk_F_type, type, sk_F: $i).
% 0.48/0.69  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.48/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.48/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.69  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.69  thf(sk_E_type, type, sk_E: $i).
% 0.48/0.69  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.69  thf(t6_tmap_1, conjecture,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.69           ( ![C:$i]:
% 0.48/0.69             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.69                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.69               ( ![D:$i]:
% 0.48/0.69                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.69                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.69                   ( ( r1_subset_1 @ C @ D ) =>
% 0.48/0.69                     ( ![E:$i]:
% 0.48/0.69                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.69                           ( m1_subset_1 @
% 0.48/0.69                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.48/0.69                         ( ![F:$i]:
% 0.48/0.69                           ( ( ( v1_funct_1 @ F ) & 
% 0.48/0.69                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.69                               ( m1_subset_1 @
% 0.48/0.69                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.69                             ( ( ( k2_partfun1 @
% 0.48/0.69                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.48/0.69                                 ( k2_partfun1 @
% 0.48/0.69                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.48/0.69                               ( ( k2_partfun1 @
% 0.48/0.69                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.69                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.48/0.69                                 ( E ) ) & 
% 0.48/0.69                               ( ( k2_partfun1 @
% 0.48/0.69                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.69                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.48/0.69                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i]:
% 0.48/0.69        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.69          ( ![B:$i]:
% 0.48/0.69            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.69              ( ![C:$i]:
% 0.48/0.69                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.69                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.69                  ( ![D:$i]:
% 0.48/0.69                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.69                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.69                      ( ( r1_subset_1 @ C @ D ) =>
% 0.48/0.69                        ( ![E:$i]:
% 0.48/0.69                          ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.69                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.69                              ( m1_subset_1 @
% 0.48/0.69                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.48/0.69                            ( ![F:$i]:
% 0.48/0.69                              ( ( ( v1_funct_1 @ F ) & 
% 0.48/0.69                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.69                                  ( m1_subset_1 @
% 0.48/0.69                                    F @ 
% 0.48/0.69                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.69                                ( ( ( k2_partfun1 @
% 0.48/0.69                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.48/0.69                                    ( k2_partfun1 @
% 0.48/0.69                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.48/0.69                                  ( ( k2_partfun1 @
% 0.48/0.69                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.69                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.48/0.69                                    ( E ) ) & 
% 0.48/0.69                                  ( ( k2_partfun1 @
% 0.48/0.69                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.69                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.48/0.69                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.48/0.69  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(dt_k1_tmap_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.69     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.48/0.69         ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.48/0.69         ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.48/0.69         ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.69         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.48/0.69         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.69         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.69       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.48/0.69         ( v1_funct_2 @
% 0.48/0.69           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.48/0.69           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.48/0.69         ( m1_subset_1 @
% 0.48/0.69           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.48/0.69           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.48/0.69          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.48/0.69          | ~ (v1_funct_1 @ X42)
% 0.48/0.69          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.48/0.69          | (v1_xboole_0 @ X45)
% 0.48/0.69          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 0.48/0.69          | (v1_xboole_0 @ X43)
% 0.48/0.69          | (v1_xboole_0 @ X44)
% 0.48/0.69          | (v1_xboole_0 @ X46)
% 0.48/0.69          | ~ (v1_funct_1 @ X47)
% 0.48/0.69          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 0.48/0.69          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.48/0.69          | (v1_funct_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47)))),
% 0.48/0.69      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.48/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.48/0.69          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.48/0.69          | ~ (v1_funct_1 @ X0)
% 0.48/0.69          | (v1_xboole_0 @ X2)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.48/0.69          | (v1_xboole_0 @ X1)
% 0.48/0.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.48/0.69          | ~ (v1_funct_1 @ sk_E)
% 0.48/0.69          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.48/0.69  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.48/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.48/0.69          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.48/0.69          | ~ (v1_funct_1 @ X0)
% 0.48/0.69          | (v1_xboole_0 @ X2)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.48/0.69          | (v1_xboole_0 @ X1)
% 0.48/0.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.48/0.69      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_D)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (v1_funct_1 @ sk_F)
% 0.48/0.69          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.48/0.69          | (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['2', '8'])).
% 0.48/0.69  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_D)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.69      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['1', '12'])).
% 0.48/0.69  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.48/0.69          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.48/0.69          | ~ (v1_funct_1 @ X42)
% 0.48/0.69          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.48/0.69          | (v1_xboole_0 @ X45)
% 0.48/0.69          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 0.48/0.69          | (v1_xboole_0 @ X43)
% 0.48/0.69          | (v1_xboole_0 @ X44)
% 0.48/0.69          | (v1_xboole_0 @ X46)
% 0.48/0.69          | ~ (v1_funct_1 @ X47)
% 0.48/0.69          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 0.48/0.69          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.48/0.69          | (v1_funct_2 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 0.48/0.69             (k4_subset_1 @ X46 @ X43 @ X45) @ X44))),
% 0.48/0.69      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.48/0.69           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.48/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.48/0.69          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.48/0.69          | ~ (v1_funct_1 @ X2)
% 0.48/0.69          | (v1_xboole_0 @ X1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.48/0.69          | ~ (v1_funct_1 @ sk_E)
% 0.48/0.69          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.48/0.69           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.48/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.48/0.69          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.48/0.69          | ~ (v1_funct_1 @ X2)
% 0.48/0.69          | (v1_xboole_0 @ X1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.69      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.48/0.69  thf('24', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_D)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (v1_funct_1 @ sk_F)
% 0.48/0.69          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.48/0.69          | (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['17', '23'])).
% 0.48/0.69  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_D)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.48/0.69      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (((v1_funct_2 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['16', '27'])).
% 0.48/0.69  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('30', plain,
% 0.48/0.69      (((v1_funct_2 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.69  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('34', plain,
% 0.48/0.69      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.48/0.69          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.48/0.69          | ~ (v1_funct_1 @ X42)
% 0.48/0.69          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.48/0.69          | (v1_xboole_0 @ X45)
% 0.48/0.69          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 0.48/0.69          | (v1_xboole_0 @ X43)
% 0.48/0.69          | (v1_xboole_0 @ X44)
% 0.48/0.69          | (v1_xboole_0 @ X46)
% 0.48/0.69          | ~ (v1_funct_1 @ X47)
% 0.48/0.69          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 0.48/0.69          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.48/0.69          | (m1_subset_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 0.48/0.69             (k1_zfmisc_1 @ 
% 0.48/0.69              (k2_zfmisc_1 @ (k4_subset_1 @ X46 @ X43 @ X45) @ X44))))),
% 0.48/0.69      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.48/0.69  thf('35', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.48/0.69           (k1_zfmisc_1 @ 
% 0.48/0.69            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.48/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.48/0.69          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.48/0.69          | ~ (v1_funct_1 @ X2)
% 0.48/0.69          | (v1_xboole_0 @ X1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.48/0.69          | ~ (v1_funct_1 @ sk_E)
% 0.48/0.69          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.69  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.48/0.69           (k1_zfmisc_1 @ 
% 0.48/0.69            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.48/0.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.48/0.69          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.48/0.69          | ~ (v1_funct_1 @ X2)
% 0.48/0.69          | (v1_xboole_0 @ X1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.69      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_D)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | ~ (v1_funct_1 @ sk_F)
% 0.48/0.69          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.48/0.69          | (m1_subset_1 @ 
% 0.48/0.69             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k1_zfmisc_1 @ 
% 0.48/0.69              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['32', '38'])).
% 0.48/0.69  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('42', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_D)
% 0.48/0.69          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69          | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69          | (v1_xboole_0 @ X0)
% 0.48/0.69          | (m1_subset_1 @ 
% 0.48/0.69             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k1_zfmisc_1 @ 
% 0.48/0.69              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.48/0.69      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.48/0.69  thf('43', plain,
% 0.48/0.69      (((m1_subset_1 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69         (k1_zfmisc_1 @ 
% 0.48/0.69          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['31', '42'])).
% 0.48/0.69  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('45', plain,
% 0.48/0.69      (((m1_subset_1 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69         (k1_zfmisc_1 @ 
% 0.48/0.69          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['43', '44'])).
% 0.48/0.69  thf(d1_tmap_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.69           ( ![C:$i]:
% 0.48/0.69             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.69                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.69               ( ![D:$i]:
% 0.48/0.69                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.69                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.69                   ( ![E:$i]:
% 0.48/0.69                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.69                         ( m1_subset_1 @
% 0.48/0.69                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.48/0.69                       ( ![F:$i]:
% 0.48/0.69                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.69                             ( m1_subset_1 @
% 0.48/0.69                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.69                           ( ( ( k2_partfun1 @
% 0.48/0.69                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.48/0.69                               ( k2_partfun1 @
% 0.48/0.69                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.48/0.69                             ( ![G:$i]:
% 0.48/0.69                               ( ( ( v1_funct_1 @ G ) & 
% 0.48/0.69                                   ( v1_funct_2 @
% 0.48/0.69                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.48/0.69                                   ( m1_subset_1 @
% 0.48/0.69                                     G @ 
% 0.48/0.69                                     ( k1_zfmisc_1 @
% 0.48/0.69                                       ( k2_zfmisc_1 @
% 0.48/0.69                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.48/0.69                                 ( ( ( G ) =
% 0.48/0.69                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.48/0.69                                   ( ( ( k2_partfun1 @
% 0.48/0.69                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.48/0.69                                         C ) =
% 0.48/0.69                                       ( E ) ) & 
% 0.48/0.69                                     ( ( k2_partfun1 @
% 0.48/0.69                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.48/0.69                                         D ) =
% 0.48/0.69                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.69  thf('46', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X35)
% 0.48/0.69          | (v1_xboole_0 @ X36)
% 0.48/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | ~ (v1_funct_1 @ X38)
% 0.48/0.69          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.48/0.69          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.48/0.69          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X40)
% 0.48/0.69              = (X39))
% 0.48/0.69          | ~ (m1_subset_1 @ X41 @ 
% 0.48/0.69               (k1_zfmisc_1 @ 
% 0.48/0.69                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.48/0.69          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.48/0.69          | ~ (v1_funct_1 @ X41)
% 0.48/0.69          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.48/0.69              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.48/0.69                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.48/0.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.48/0.69          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.48/0.69          | ~ (v1_funct_1 @ X39)
% 0.48/0.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | (v1_xboole_0 @ X40)
% 0.48/0.69          | (v1_xboole_0 @ X37))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.48/0.69  thf('47', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X37)
% 0.48/0.69          | (v1_xboole_0 @ X40)
% 0.48/0.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | ~ (v1_funct_1 @ X39)
% 0.48/0.69          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.48/0.69          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.48/0.69              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.48/0.69                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.48/0.69          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.48/0.69          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.48/0.69               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.48/0.69               (k1_zfmisc_1 @ 
% 0.48/0.69                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.48/0.69          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 0.48/0.69              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X40) = (
% 0.48/0.69              X39))
% 0.48/0.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.48/0.69          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.48/0.69          | ~ (v1_funct_1 @ X38)
% 0.48/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | (v1_xboole_0 @ X36)
% 0.48/0.69          | (v1_xboole_0 @ X35))),
% 0.48/0.69      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.69  thf('48', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | ~ (v1_funct_1 @ sk_F)
% 0.48/0.69        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69            = (sk_E))
% 0.48/0.69        | ~ (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | ~ (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.48/0.69        | ~ (m1_subset_1 @ sk_E @ 
% 0.48/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.48/0.69        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.48/0.69        | ~ (v1_funct_1 @ sk_E)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['45', '47'])).
% 0.48/0.69  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('52', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(redefinition_k9_subset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.69       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.48/0.69  thf('54', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.48/0.69         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.48/0.69          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.48/0.69  thf('55', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(redefinition_r1_subset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.48/0.69       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.48/0.69  thf('57', plain,
% 0.48/0.69      (![X26 : $i, X27 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X26)
% 0.48/0.69          | (v1_xboole_0 @ X27)
% 0.48/0.69          | (r1_xboole_0 @ X26 @ X27)
% 0.48/0.69          | ~ (r1_subset_1 @ X26 @ X27))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.48/0.69  thf('58', plain,
% 0.48/0.69      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.69  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.48/0.69      inference('clc', [status(thm)], ['58', '59'])).
% 0.48/0.69  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.48/0.69      inference('clc', [status(thm)], ['60', '61'])).
% 0.48/0.69  thf(d7_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.48/0.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.69  thf('63', plain,
% 0.48/0.69      (![X3 : $i, X4 : $i]:
% 0.48/0.69         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.48/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.69  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('65', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(redefinition_k2_partfun1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.69       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.48/0.69  thf('66', plain,
% 0.48/0.69      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.48/0.69          | ~ (v1_funct_1 @ X31)
% 0.48/0.69          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.48/0.69  thf('67', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.48/0.69            = (k7_relat_1 @ sk_E @ X0))
% 0.48/0.69          | ~ (v1_funct_1 @ sk_E))),
% 0.48/0.69      inference('sup-', [status(thm)], ['65', '66'])).
% 0.48/0.69  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('69', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.48/0.69           = (k7_relat_1 @ sk_E @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.69  thf('70', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(cc2_relset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.69  thf('71', plain,
% 0.48/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.69         ((v4_relat_1 @ X28 @ X29)
% 0.48/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.69  thf('72', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 0.48/0.69      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.69  thf(t209_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.48/0.69       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.48/0.69  thf('73', plain,
% 0.48/0.69      (![X24 : $i, X25 : $i]:
% 0.48/0.69         (((X24) = (k7_relat_1 @ X24 @ X25))
% 0.48/0.69          | ~ (v4_relat_1 @ X24 @ X25)
% 0.48/0.69          | ~ (v1_relat_1 @ X24))),
% 0.48/0.69      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.69  thf('74', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C_1)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['72', '73'])).
% 0.48/0.69  thf('75', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(cc2_relat_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.69  thf('76', plain,
% 0.48/0.69      (![X17 : $i, X18 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.48/0.69          | (v1_relat_1 @ X17)
% 0.48/0.69          | ~ (v1_relat_1 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.69  thf('77', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)) | (v1_relat_1 @ sk_E))),
% 0.48/0.69      inference('sup-', [status(thm)], ['75', '76'])).
% 0.48/0.69  thf(fc6_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.69  thf('78', plain,
% 0.48/0.69      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.69  thf('79', plain, ((v1_relat_1 @ sk_E)),
% 0.48/0.69      inference('demod', [status(thm)], ['77', '78'])).
% 0.48/0.69  thf('80', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C_1))),
% 0.48/0.69      inference('demod', [status(thm)], ['74', '79'])).
% 0.48/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.69  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.69  thf(t3_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.48/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.48/0.69  thf('82', plain,
% 0.48/0.69      (![X6 : $i, X7 : $i]:
% 0.48/0.69         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.48/0.69  thf(d1_xboole_0, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.69  thf('83', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.69  thf('84', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.48/0.69  thf('85', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.48/0.69      inference('sup-', [status(thm)], ['81', '84'])).
% 0.48/0.69  thf(t207_relat_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( v1_relat_1 @ C ) =>
% 0.48/0.69       ( ( r1_xboole_0 @ A @ B ) =>
% 0.48/0.69         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.69  thf('86', plain,
% 0.48/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.69         (~ (r1_xboole_0 @ X21 @ X22)
% 0.48/0.69          | ~ (v1_relat_1 @ X23)
% 0.48/0.69          | ((k7_relat_1 @ (k7_relat_1 @ X23 @ X21) @ X22) = (k1_xboole_0)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.48/0.69  thf('87', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.69          | ~ (v1_relat_1 @ X1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['85', '86'])).
% 0.48/0.69  thf('88', plain,
% 0.48/0.69      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.69        | ~ (v1_relat_1 @ sk_E))),
% 0.48/0.69      inference('sup+', [status(thm)], ['80', '87'])).
% 0.48/0.69  thf('89', plain, ((v1_relat_1 @ sk_E)),
% 0.48/0.69      inference('demod', [status(thm)], ['77', '78'])).
% 0.48/0.69  thf('90', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.48/0.69  thf('91', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('92', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('93', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('94', plain,
% 0.48/0.69      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.48/0.69          | ~ (v1_funct_1 @ X31)
% 0.48/0.69          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.48/0.69  thf('95', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.48/0.69          | ~ (v1_funct_1 @ sk_F))),
% 0.48/0.69      inference('sup-', [status(thm)], ['93', '94'])).
% 0.48/0.69  thf('96', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('97', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['95', '96'])).
% 0.48/0.69  thf('98', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('99', plain,
% 0.48/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.69         ((v4_relat_1 @ X28 @ X29)
% 0.48/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.69  thf('100', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.48/0.69      inference('sup-', [status(thm)], ['98', '99'])).
% 0.48/0.69  thf('101', plain,
% 0.48/0.69      (![X24 : $i, X25 : $i]:
% 0.48/0.69         (((X24) = (k7_relat_1 @ X24 @ X25))
% 0.48/0.69          | ~ (v4_relat_1 @ X24 @ X25)
% 0.48/0.69          | ~ (v1_relat_1 @ X24))),
% 0.48/0.69      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.69  thf('102', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['100', '101'])).
% 0.48/0.69  thf('103', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('104', plain,
% 0.48/0.69      (![X17 : $i, X18 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.48/0.69          | (v1_relat_1 @ X17)
% 0.48/0.69          | ~ (v1_relat_1 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.69  thf('105', plain,
% 0.48/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)) | (v1_relat_1 @ sk_F))),
% 0.48/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.48/0.69  thf('106', plain,
% 0.48/0.69      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.69  thf('107', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.69      inference('demod', [status(thm)], ['105', '106'])).
% 0.48/0.69  thf('108', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['102', '107'])).
% 0.48/0.69  thf('109', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.69          | ~ (v1_relat_1 @ X1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['85', '86'])).
% 0.48/0.69  thf('110', plain,
% 0.48/0.69      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.69        | ~ (v1_relat_1 @ sk_F))),
% 0.48/0.69      inference('sup+', [status(thm)], ['108', '109'])).
% 0.48/0.69  thf('111', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.69      inference('demod', [status(thm)], ['105', '106'])).
% 0.48/0.69  thf('112', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['110', '111'])).
% 0.48/0.69  thf('113', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('114', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('115', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('116', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('117', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69            = (sk_E))
% 0.48/0.69        | ~ (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | ~ (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A))),
% 0.48/0.69      inference('demod', [status(thm)],
% 0.48/0.69                ['48', '49', '50', '51', '52', '55', '64', '69', '90', '91', 
% 0.48/0.69                 '92', '97', '112', '113', '114', '115', '116'])).
% 0.48/0.69  thf('118', plain,
% 0.48/0.69      ((~ (v1_funct_1 @ 
% 0.48/0.69           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ~ (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69            = (sk_E))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify', [status(thm)], ['117'])).
% 0.48/0.69  thf('119', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69            = (sk_E))
% 0.48/0.69        | ~ (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['30', '118'])).
% 0.48/0.69  thf('120', plain,
% 0.48/0.69      ((~ (v1_funct_1 @ 
% 0.48/0.69           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69            = (sk_E))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify', [status(thm)], ['119'])).
% 0.48/0.69  thf('121', plain,
% 0.48/0.69      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69            != (sk_E))
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            != (sk_F)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('122', plain,
% 0.48/0.69      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69          != (sk_E)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_C_1) = (sk_E))))),
% 0.48/0.69      inference('split', [status(esa)], ['121'])).
% 0.48/0.69  thf('123', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['95', '96'])).
% 0.48/0.69  thf('124', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('125', plain,
% 0.48/0.69      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.48/0.69      inference('split', [status(esa)], ['121'])).
% 0.48/0.69  thf('126', plain,
% 0.48/0.69      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['124', '125'])).
% 0.48/0.69  thf('127', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('128', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('129', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('130', plain,
% 0.48/0.69      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0)
% 0.48/0.69          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.48/0.69      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.48/0.69  thf('131', plain,
% 0.48/0.69      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0)
% 0.48/0.69          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['123', '130'])).
% 0.48/0.69  thf('132', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.48/0.69           = (k7_relat_1 @ sk_E @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.69  thf('133', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.48/0.69  thf('134', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['110', '111'])).
% 0.48/0.69  thf('135', plain,
% 0.48/0.69      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.48/0.69      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.48/0.69  thf('136', plain,
% 0.48/0.69      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.48/0.69      inference('simplify', [status(thm)], ['135'])).
% 0.48/0.69  thf('137', plain,
% 0.48/0.69      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('138', plain,
% 0.48/0.69      (((v1_funct_2 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.69  thf('139', plain,
% 0.48/0.69      (((m1_subset_1 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69         (k1_zfmisc_1 @ 
% 0.48/0.69          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('demod', [status(thm)], ['43', '44'])).
% 0.48/0.69  thf('140', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X35)
% 0.48/0.69          | (v1_xboole_0 @ X36)
% 0.48/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | ~ (v1_funct_1 @ X38)
% 0.48/0.69          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.48/0.69          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.48/0.69          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X36)
% 0.48/0.69              = (X38))
% 0.48/0.69          | ~ (m1_subset_1 @ X41 @ 
% 0.48/0.69               (k1_zfmisc_1 @ 
% 0.48/0.69                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.48/0.69          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.48/0.69          | ~ (v1_funct_1 @ X41)
% 0.48/0.69          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.48/0.69              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.48/0.69                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.48/0.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.48/0.69          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.48/0.69          | ~ (v1_funct_1 @ X39)
% 0.48/0.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | (v1_xboole_0 @ X40)
% 0.48/0.69          | (v1_xboole_0 @ X37))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.48/0.69  thf('141', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X37)
% 0.48/0.69          | (v1_xboole_0 @ X40)
% 0.48/0.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | ~ (v1_funct_1 @ X39)
% 0.48/0.69          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.48/0.69          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.48/0.69              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.48/0.69                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.48/0.69          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.48/0.69          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.48/0.69               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.48/0.69               (k1_zfmisc_1 @ 
% 0.48/0.69                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.48/0.69          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 0.48/0.69              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X36) = (
% 0.48/0.69              X38))
% 0.48/0.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.48/0.69          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.48/0.69          | ~ (v1_funct_1 @ X38)
% 0.48/0.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.48/0.69          | (v1_xboole_0 @ X36)
% 0.48/0.69          | (v1_xboole_0 @ X35))),
% 0.48/0.69      inference('simplify', [status(thm)], ['140'])).
% 0.48/0.69  thf('142', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | ~ (v1_funct_1 @ sk_F)
% 0.48/0.69        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            = (sk_F))
% 0.48/0.69        | ~ (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | ~ (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.48/0.69        | ~ (m1_subset_1 @ sk_E @ 
% 0.48/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.48/0.69        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.48/0.69        | ~ (v1_funct_1 @ sk_E)
% 0.48/0.69        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['139', '141'])).
% 0.48/0.69  thf('143', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('144', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('145', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('146', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('147', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('148', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('149', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.48/0.69           = (k7_relat_1 @ sk_E @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.69  thf('150', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.48/0.69  thf('151', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('152', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('153', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['95', '96'])).
% 0.48/0.69  thf('154', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['110', '111'])).
% 0.48/0.69  thf('155', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('156', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('157', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('158', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('159', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            = (sk_F))
% 0.48/0.69        | ~ (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | ~ (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A))),
% 0.48/0.69      inference('demod', [status(thm)],
% 0.48/0.69                ['142', '143', '144', '145', '146', '147', '148', '149', 
% 0.48/0.69                 '150', '151', '152', '153', '154', '155', '156', '157', '158'])).
% 0.48/0.69  thf('160', plain,
% 0.48/0.69      ((~ (v1_funct_1 @ 
% 0.48/0.69           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ~ (v1_funct_2 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            = (sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify', [status(thm)], ['159'])).
% 0.48/0.69  thf('161', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            = (sk_F))
% 0.48/0.69        | ~ (v1_funct_1 @ 
% 0.48/0.69             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['138', '160'])).
% 0.48/0.69  thf('162', plain,
% 0.48/0.69      ((~ (v1_funct_1 @ 
% 0.48/0.69           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            = (sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify', [status(thm)], ['161'])).
% 0.48/0.69  thf('163', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69            = (sk_F)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['137', '162'])).
% 0.48/0.69  thf('164', plain,
% 0.48/0.69      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69          = (sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify', [status(thm)], ['163'])).
% 0.48/0.69  thf('165', plain,
% 0.48/0.69      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69          != (sk_F)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_D) = (sk_F))))),
% 0.48/0.69      inference('split', [status(esa)], ['121'])).
% 0.48/0.69  thf('166', plain,
% 0.48/0.69      (((((sk_F) != (sk_F))
% 0.48/0.69         | (v1_xboole_0 @ sk_D)
% 0.48/0.69         | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69         | (v1_xboole_0 @ sk_A)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_D) = (sk_F))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['164', '165'])).
% 0.48/0.69  thf('167', plain,
% 0.48/0.69      ((((v1_xboole_0 @ sk_A)
% 0.48/0.69         | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69         | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69         | (v1_xboole_0 @ sk_D)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_D) = (sk_F))))),
% 0.48/0.69      inference('simplify', [status(thm)], ['166'])).
% 0.48/0.69  thf('168', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('169', plain,
% 0.48/0.69      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_D) = (sk_F))))),
% 0.48/0.69      inference('sup-', [status(thm)], ['167', '168'])).
% 0.48/0.69  thf('170', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('171', plain,
% 0.48/0.69      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_D) = (sk_F))))),
% 0.48/0.69      inference('clc', [status(thm)], ['169', '170'])).
% 0.48/0.69  thf('172', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('173', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_B_1))
% 0.48/0.69         <= (~
% 0.48/0.69             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.69                sk_D) = (sk_F))))),
% 0.48/0.69      inference('clc', [status(thm)], ['171', '172'])).
% 0.48/0.69  thf('174', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('175', plain,
% 0.48/0.69      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69          = (sk_F)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['173', '174'])).
% 0.48/0.69  thf('176', plain,
% 0.48/0.69      (~
% 0.48/0.69       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69          = (sk_E))) | 
% 0.48/0.69       ~
% 0.48/0.69       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.69          = (sk_F))) | 
% 0.48/0.69       ~
% 0.48/0.69       (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.48/0.69          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.48/0.69          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.48/0.69             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.48/0.69      inference('split', [status(esa)], ['121'])).
% 0.48/0.69  thf('177', plain,
% 0.48/0.69      (~
% 0.48/0.69       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69          = (sk_E)))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['136', '175', '176'])).
% 0.48/0.69  thf('178', plain,
% 0.48/0.69      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.48/0.69         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.48/0.69         != (sk_E))),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['122', '177'])).
% 0.48/0.69  thf('179', plain,
% 0.48/0.69      ((~ (v1_funct_1 @ 
% 0.48/0.69           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify_reflect-', [status(thm)], ['120', '178'])).
% 0.48/0.69  thf('180', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_D)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['15', '179'])).
% 0.48/0.69  thf('181', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_C_1)
% 0.48/0.69        | (v1_xboole_0 @ sk_D))),
% 0.48/0.69      inference('simplify', [status(thm)], ['180'])).
% 0.48/0.69  thf('182', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('183', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['181', '182'])).
% 0.48/0.69  thf('184', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('185', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.48/0.69      inference('clc', [status(thm)], ['183', '184'])).
% 0.48/0.69  thf('186', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('187', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.48/0.69      inference('clc', [status(thm)], ['185', '186'])).
% 0.48/0.69  thf('188', plain, ($false), inference('demod', [status(thm)], ['0', '187'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
