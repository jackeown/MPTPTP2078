%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oqpRXSdfkv

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:02 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 903 expanded)
%              Number of leaves         :   43 ( 279 expanded)
%              Depth                    :   35
%              Number of atoms          : 3703 (37510 expanded)
%              Number of equality atoms :  115 (1202 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43 ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43 ) @ ( k4_subset_1 @ X42 @ X39 @ X41 ) @ X40 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X42 @ X39 @ X41 ) @ X40 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( X37
       != ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ X37 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
       => ( r1_subset_1 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ( r1_subset_1 @ X15 @ X14 )
      | ~ ( r1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_subset_1])).

thf('63',plain,
    ( ( r1_subset_1 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_subset_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_subset_1 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['65','66'])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('69',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['79','80'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('82',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('88',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('89',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['83','86','89'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['84','85'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','94'])).

thf(t108_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('96',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X7 @ X8 ) @ ( k7_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ X0 @ sk_D ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ sk_E @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('98',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('99',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['84','85'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ X0 @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('109',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('126',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['123','126','129'])).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','134'])).

thf('136',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X7 @ X8 ) @ ( k7_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_relat_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ X0 ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k7_relat_1 @ sk_F @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('138',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['124','125'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','60','100','101','106','142','143','144','145','146'])).

thf('148',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('153',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['149'])).

thf('154',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('156',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ X0 @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','140','141'])).

thf('161',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('164',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('165',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('166',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( X37
       != ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ X37 @ X32 )
        = X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('167',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ X32 )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
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
    inference('sup-',[status(thm)],['165','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ X0 @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','140','141'])).

thf('179',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
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
    inference(demod,[status(thm)],['168','169','170','171','172','173','174','175','176','177','178','179','180','181','182'])).

thf('184',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
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
    inference('sup-',[status(thm)],['164','184'])).

thf('186',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
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
    inference('sup-',[status(thm)],['163','186'])).

thf('188',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['149'])).

thf('190',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['149'])).

thf('201',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['162','199','200'])).

thf('202',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['150','201'])).

thf('203',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['148','202'])).

thf('204',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','203'])).

thf('205',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','205'])).

thf('207',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    $false ),
    inference(demod,[status(thm)],['0','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oqpRXSdfkv
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.71  % Solved by: fo/fo7.sh
% 0.44/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.71  % done 514 iterations in 0.247s
% 0.44/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.71  % SZS output start Refutation
% 0.44/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.71  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.71  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.71  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.71  thf(t6_tmap_1, conjecture,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.71           ( ![C:$i]:
% 0.44/0.71             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.71                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.71               ( ![D:$i]:
% 0.44/0.71                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.71                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.71                   ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.71                     ( ![E:$i]:
% 0.44/0.71                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.71                           ( m1_subset_1 @
% 0.44/0.71                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.71                         ( ![F:$i]:
% 0.44/0.71                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.71                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.71                               ( m1_subset_1 @
% 0.44/0.71                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.71                             ( ( ( k2_partfun1 @
% 0.44/0.71                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.71                                 ( k2_partfun1 @
% 0.44/0.71                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.71                               ( ( k2_partfun1 @
% 0.44/0.71                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.71                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.71                                 ( E ) ) & 
% 0.44/0.71                               ( ( k2_partfun1 @
% 0.44/0.71                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.71                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.71                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.71    (~( ![A:$i]:
% 0.44/0.71        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.71          ( ![B:$i]:
% 0.44/0.71            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.71              ( ![C:$i]:
% 0.44/0.71                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.71                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.71                  ( ![D:$i]:
% 0.44/0.71                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.71                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.71                      ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.71                        ( ![E:$i]:
% 0.44/0.71                          ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.71                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.71                              ( m1_subset_1 @
% 0.44/0.71                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.71                            ( ![F:$i]:
% 0.44/0.71                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.71                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.71                                  ( m1_subset_1 @
% 0.44/0.71                                    F @ 
% 0.44/0.71                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.71                                ( ( ( k2_partfun1 @
% 0.44/0.71                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.71                                    ( k2_partfun1 @
% 0.44/0.71                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.71                                  ( ( k2_partfun1 @
% 0.44/0.71                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.71                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.71                                    ( E ) ) & 
% 0.44/0.71                                  ( ( k2_partfun1 @
% 0.44/0.71                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.71                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.71                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.71    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.44/0.71  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('2', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('3', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(dt_k1_tmap_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.71         ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.71         ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.44/0.71         ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.44/0.71         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.71       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.71         ( v1_funct_2 @
% 0.44/0.71           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.71           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.71         ( m1_subset_1 @
% 0.44/0.71           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.44/0.71  thf('4', plain,
% 0.44/0.71      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.44/0.71          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.44/0.71          | ~ (v1_funct_1 @ X38)
% 0.44/0.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.44/0.71          | (v1_xboole_0 @ X41)
% 0.44/0.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 0.44/0.71          | (v1_xboole_0 @ X39)
% 0.44/0.71          | (v1_xboole_0 @ X40)
% 0.44/0.71          | (v1_xboole_0 @ X42)
% 0.44/0.71          | ~ (v1_funct_1 @ X43)
% 0.44/0.71          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.44/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.44/0.71          | (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43)))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.71  thf('5', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ X0)
% 0.44/0.71          | (v1_xboole_0 @ X2)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.71          | (v1_xboole_0 @ X1)
% 0.44/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.71          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.71  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('8', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ X0)
% 0.44/0.71          | (v1_xboole_0 @ X2)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.71          | (v1_xboole_0 @ X1)
% 0.44/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.71      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.44/0.71  thf('9', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_D)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.71          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.71          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.71  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('12', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_D)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.71      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.44/0.71  thf('13', plain,
% 0.44/0.71      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['1', '12'])).
% 0.44/0.71  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('15', plain,
% 0.44/0.71      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.71  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('17', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('18', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('19', plain,
% 0.44/0.71      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.44/0.71          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.44/0.71          | ~ (v1_funct_1 @ X38)
% 0.44/0.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.44/0.71          | (v1_xboole_0 @ X41)
% 0.44/0.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 0.44/0.71          | (v1_xboole_0 @ X39)
% 0.44/0.71          | (v1_xboole_0 @ X40)
% 0.44/0.71          | (v1_xboole_0 @ X42)
% 0.44/0.71          | ~ (v1_funct_1 @ X43)
% 0.44/0.71          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.44/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.44/0.71          | (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 0.44/0.71             (k4_subset_1 @ X42 @ X39 @ X41) @ X40))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.71  thf('20', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.71           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.71          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ X2)
% 0.44/0.71          | (v1_xboole_0 @ X1)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.71          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.71  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('23', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.71           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.71          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ X2)
% 0.44/0.71          | (v1_xboole_0 @ X1)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.71      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.71  thf('24', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_D)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.71          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.71          | (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['17', '23'])).
% 0.44/0.71  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('27', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_D)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.71      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.71  thf('28', plain,
% 0.44/0.71      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['16', '27'])).
% 0.44/0.71  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('30', plain,
% 0.44/0.71      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.71  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('32', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('33', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('34', plain,
% 0.44/0.71      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.44/0.71          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.44/0.71          | ~ (v1_funct_1 @ X38)
% 0.44/0.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.44/0.71          | (v1_xboole_0 @ X41)
% 0.44/0.71          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 0.44/0.71          | (v1_xboole_0 @ X39)
% 0.44/0.71          | (v1_xboole_0 @ X40)
% 0.44/0.71          | (v1_xboole_0 @ X42)
% 0.44/0.71          | ~ (v1_funct_1 @ X43)
% 0.44/0.71          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.44/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.44/0.71          | (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 0.44/0.71             (k1_zfmisc_1 @ 
% 0.44/0.71              (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X39 @ X41) @ X40))))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.71  thf('35', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.71          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ X2)
% 0.44/0.71          | (v1_xboole_0 @ X1)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.71          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.71  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('38', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.71          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.71          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ X2)
% 0.44/0.71          | (v1_xboole_0 @ X1)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.44/0.71  thf('39', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_D)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.71          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.71          | (m1_subset_1 @ 
% 0.44/0.71             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k1_zfmisc_1 @ 
% 0.44/0.71              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['32', '38'])).
% 0.44/0.71  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('42', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_D)
% 0.44/0.71          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.71          | (v1_xboole_0 @ sk_C)
% 0.44/0.71          | (v1_xboole_0 @ sk_B)
% 0.44/0.71          | (v1_xboole_0 @ X0)
% 0.44/0.71          | (m1_subset_1 @ 
% 0.44/0.71             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k1_zfmisc_1 @ 
% 0.44/0.71              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.71      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.71  thf('43', plain,
% 0.44/0.71      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71         (k1_zfmisc_1 @ 
% 0.44/0.71          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['31', '42'])).
% 0.44/0.71  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('45', plain,
% 0.44/0.71      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71         (k1_zfmisc_1 @ 
% 0.44/0.71          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.71  thf(d1_tmap_1, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.71           ( ![C:$i]:
% 0.44/0.71             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.71                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.71               ( ![D:$i]:
% 0.44/0.71                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.71                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.71                   ( ![E:$i]:
% 0.44/0.71                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.71                         ( m1_subset_1 @
% 0.44/0.71                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.71                       ( ![F:$i]:
% 0.44/0.71                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.71                             ( m1_subset_1 @
% 0.44/0.71                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.71                           ( ( ( k2_partfun1 @
% 0.44/0.71                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.71                               ( k2_partfun1 @
% 0.44/0.71                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.44/0.71                             ( ![G:$i]:
% 0.44/0.71                               ( ( ( v1_funct_1 @ G ) & 
% 0.44/0.71                                   ( v1_funct_2 @
% 0.44/0.71                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.71                                   ( m1_subset_1 @
% 0.44/0.71                                     G @ 
% 0.44/0.71                                     ( k1_zfmisc_1 @
% 0.44/0.71                                       ( k2_zfmisc_1 @
% 0.44/0.71                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.44/0.71                                 ( ( ( G ) =
% 0.44/0.71                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.71                                   ( ( ( k2_partfun1 @
% 0.44/0.71                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.71                                         C ) =
% 0.44/0.71                                       ( E ) ) & 
% 0.44/0.71                                     ( ( k2_partfun1 @
% 0.44/0.71                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.71                                         D ) =
% 0.44/0.71                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.71  thf('46', plain,
% 0.44/0.71      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X31)
% 0.44/0.71          | (v1_xboole_0 @ X32)
% 0.44/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | ~ (v1_funct_1 @ X34)
% 0.44/0.71          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.44/0.71          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.44/0.71          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 0.44/0.71          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X36)
% 0.44/0.71              = (X35))
% 0.44/0.71          | ~ (m1_subset_1 @ X37 @ 
% 0.44/0.71               (k1_zfmisc_1 @ 
% 0.44/0.71                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 0.44/0.71          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 0.44/0.71          | ~ (v1_funct_1 @ X37)
% 0.44/0.71          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 0.44/0.71              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 0.44/0.71                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 0.44/0.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 0.44/0.71          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 0.44/0.71          | ~ (v1_funct_1 @ X35)
% 0.44/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | (v1_xboole_0 @ X36)
% 0.44/0.71          | (v1_xboole_0 @ X33))),
% 0.44/0.71      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.71  thf('47', plain,
% 0.44/0.71      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X33)
% 0.44/0.71          | (v1_xboole_0 @ X36)
% 0.44/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | ~ (v1_funct_1 @ X35)
% 0.44/0.71          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 0.44/0.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 0.44/0.71          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 0.44/0.71              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 0.44/0.71                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 0.44/0.71          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 0.44/0.71          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 0.44/0.71               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 0.44/0.71          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 0.44/0.71               (k1_zfmisc_1 @ 
% 0.44/0.71                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 0.44/0.71          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 0.44/0.71              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X36) = (
% 0.44/0.71              X35))
% 0.44/0.71          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.44/0.71          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.44/0.71          | ~ (v1_funct_1 @ X34)
% 0.44/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | (v1_xboole_0 @ X32)
% 0.44/0.71          | (v1_xboole_0 @ X31))),
% 0.44/0.71      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.71  thf('48', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71            = (sk_E))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.71        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.71        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_A))),
% 0.44/0.71      inference('sup-', [status(thm)], ['45', '47'])).
% 0.44/0.71  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('52', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.71       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.71  thf('54', plain,
% 0.44/0.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.71         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.44/0.71          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.71  thf('55', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.71  thf('56', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.71     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.71       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.71  thf('57', plain,
% 0.44/0.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.71          | ~ (v1_funct_1 @ X27)
% 0.44/0.71          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.71  thf('58', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.71          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.71  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('60', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.71  thf('61', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(symmetry_r1_subset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.71       ( ( r1_subset_1 @ A @ B ) => ( r1_subset_1 @ B @ A ) ) ))).
% 0.44/0.71  thf('62', plain,
% 0.44/0.71      (![X14 : $i, X15 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X14)
% 0.44/0.71          | (v1_xboole_0 @ X15)
% 0.44/0.71          | (r1_subset_1 @ X15 @ X14)
% 0.44/0.71          | ~ (r1_subset_1 @ X14 @ X15))),
% 0.44/0.71      inference('cnf', [status(esa)], [symmetry_r1_subset_1])).
% 0.44/0.71  thf('63', plain,
% 0.44/0.71      (((r1_subset_1 @ sk_D @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C))),
% 0.44/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.44/0.71  thf('64', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('65', plain, (((v1_xboole_0 @ sk_C) | (r1_subset_1 @ sk_D @ sk_C))),
% 0.44/0.71      inference('clc', [status(thm)], ['63', '64'])).
% 0.44/0.71  thf('66', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('67', plain, ((r1_subset_1 @ sk_D @ sk_C)),
% 0.44/0.71      inference('clc', [status(thm)], ['65', '66'])).
% 0.44/0.71  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.71       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.71  thf('68', plain,
% 0.44/0.71      (![X12 : $i, X13 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X12)
% 0.44/0.71          | (v1_xboole_0 @ X13)
% 0.44/0.71          | (r1_xboole_0 @ X12 @ X13)
% 0.44/0.71          | ~ (r1_subset_1 @ X12 @ X13))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.71  thf('69', plain,
% 0.44/0.71      (((r1_xboole_0 @ sk_D @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.44/0.71  thf('70', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('71', plain, (((v1_xboole_0 @ sk_D) | (r1_xboole_0 @ sk_D @ sk_C))),
% 0.44/0.71      inference('clc', [status(thm)], ['69', '70'])).
% 0.44/0.71  thf('72', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('73', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.44/0.71      inference('clc', [status(thm)], ['71', '72'])).
% 0.44/0.71  thf('74', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(cc5_funct_2, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.71       ( ![C:$i]:
% 0.44/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.71  thf('75', plain,
% 0.44/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.44/0.71          | (v1_partfun1 @ X22 @ X23)
% 0.44/0.71          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.44/0.71          | ~ (v1_funct_1 @ X22)
% 0.44/0.71          | (v1_xboole_0 @ X24))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.71  thf('76', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.71        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.71      inference('sup-', [status(thm)], ['74', '75'])).
% 0.44/0.71  thf('77', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('78', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('79', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.44/0.71  thf('80', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('81', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.44/0.71      inference('clc', [status(thm)], ['79', '80'])).
% 0.44/0.71  thf(d4_partfun1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.71  thf('82', plain,
% 0.44/0.71      (![X25 : $i, X26 : $i]:
% 0.44/0.71         (~ (v1_partfun1 @ X26 @ X25)
% 0.44/0.71          | ((k1_relat_1 @ X26) = (X25))
% 0.44/0.71          | ~ (v4_relat_1 @ X26 @ X25)
% 0.44/0.71          | ~ (v1_relat_1 @ X26))),
% 0.44/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.71  thf('83', plain,
% 0.44/0.71      ((~ (v1_relat_1 @ sk_E)
% 0.44/0.71        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.44/0.71        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['81', '82'])).
% 0.44/0.71  thf('84', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(cc1_relset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.71       ( v1_relat_1 @ C ) ))).
% 0.44/0.71  thf('85', plain,
% 0.44/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.71         ((v1_relat_1 @ X16)
% 0.44/0.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.71  thf('86', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.71      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.71  thf('87', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(cc2_relset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.71  thf('88', plain,
% 0.44/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.71         ((v4_relat_1 @ X19 @ X20)
% 0.44/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.71  thf('89', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.44/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.44/0.71  thf('90', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.44/0.71      inference('demod', [status(thm)], ['83', '86', '89'])).
% 0.44/0.71  thf(t187_relat_1, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( v1_relat_1 @ A ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.71           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.71  thf('91', plain,
% 0.44/0.71      (![X10 : $i, X11 : $i]:
% 0.44/0.71         (~ (r1_xboole_0 @ X10 @ (k1_relat_1 @ X11))
% 0.44/0.71          | ((k7_relat_1 @ X11 @ X10) = (k1_xboole_0))
% 0.44/0.71          | ~ (v1_relat_1 @ X11))),
% 0.44/0.71      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.71  thf('92', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.71          | ~ (v1_relat_1 @ sk_E)
% 0.44/0.71          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['90', '91'])).
% 0.44/0.71  thf('93', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.71      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.71  thf('94', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.71          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.71      inference('demod', [status(thm)], ['92', '93'])).
% 0.44/0.71  thf('95', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['73', '94'])).
% 0.44/0.71  thf(t108_relat_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( v1_relat_1 @ C ) =>
% 0.44/0.71       ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.44/0.71         ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.44/0.71  thf('96', plain,
% 0.44/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.71         (((k7_relat_1 @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 0.44/0.71            = (k3_xboole_0 @ (k7_relat_1 @ X7 @ X8) @ (k7_relat_1 @ X7 @ X9)))
% 0.44/0.71          | ~ (v1_relat_1 @ X7))),
% 0.44/0.71      inference('cnf', [status(esa)], [t108_relat_1])).
% 0.44/0.71  thf('97', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((k7_relat_1 @ sk_E @ (k3_xboole_0 @ X0 @ sk_D))
% 0.44/0.71            = (k3_xboole_0 @ (k7_relat_1 @ sk_E @ X0) @ k1_xboole_0))
% 0.44/0.71          | ~ (v1_relat_1 @ sk_E))),
% 0.44/0.71      inference('sup+', [status(thm)], ['95', '96'])).
% 0.44/0.71  thf(t2_boole, axiom,
% 0.44/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.71  thf('98', plain,
% 0.44/0.71      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.71  thf('99', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.71      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.71  thf('100', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.44/0.71  thf('101', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.71  thf('102', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('103', plain,
% 0.44/0.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.71          | ~ (v1_funct_1 @ X27)
% 0.44/0.71          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.71  thf('104', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.71          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.71      inference('sup-', [status(thm)], ['102', '103'])).
% 0.44/0.71  thf('105', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('106', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['104', '105'])).
% 0.44/0.71  thf('107', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('108', plain,
% 0.44/0.71      (![X12 : $i, X13 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X12)
% 0.44/0.71          | (v1_xboole_0 @ X13)
% 0.44/0.71          | (r1_xboole_0 @ X12 @ X13)
% 0.44/0.71          | ~ (r1_subset_1 @ X12 @ X13))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.71  thf('109', plain,
% 0.44/0.71      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C))),
% 0.44/0.71      inference('sup-', [status(thm)], ['107', '108'])).
% 0.44/0.71  thf('110', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('111', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.71      inference('clc', [status(thm)], ['109', '110'])).
% 0.44/0.71  thf('112', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('113', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.44/0.71      inference('clc', [status(thm)], ['111', '112'])).
% 0.44/0.71  thf('114', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('115', plain,
% 0.44/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.44/0.71          | (v1_partfun1 @ X22 @ X23)
% 0.44/0.71          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.44/0.71          | ~ (v1_funct_1 @ X22)
% 0.44/0.71          | (v1_xboole_0 @ X24))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.71  thf('116', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.71        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['114', '115'])).
% 0.44/0.71  thf('117', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('118', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('119', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.44/0.71  thf('120', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('121', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.44/0.71      inference('clc', [status(thm)], ['119', '120'])).
% 0.44/0.71  thf('122', plain,
% 0.44/0.71      (![X25 : $i, X26 : $i]:
% 0.44/0.71         (~ (v1_partfun1 @ X26 @ X25)
% 0.44/0.71          | ((k1_relat_1 @ X26) = (X25))
% 0.44/0.71          | ~ (v4_relat_1 @ X26 @ X25)
% 0.44/0.71          | ~ (v1_relat_1 @ X26))),
% 0.44/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.71  thf('123', plain,
% 0.44/0.71      ((~ (v1_relat_1 @ sk_F)
% 0.44/0.71        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.44/0.71        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['121', '122'])).
% 0.44/0.71  thf('124', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('125', plain,
% 0.44/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.71         ((v1_relat_1 @ X16)
% 0.44/0.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.71  thf('126', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.71      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.71  thf('127', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('128', plain,
% 0.44/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.71         ((v4_relat_1 @ X19 @ X20)
% 0.44/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.71  thf('129', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.44/0.71      inference('sup-', [status(thm)], ['127', '128'])).
% 0.44/0.71  thf('130', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['123', '126', '129'])).
% 0.44/0.71  thf('131', plain,
% 0.44/0.71      (![X10 : $i, X11 : $i]:
% 0.44/0.71         (~ (r1_xboole_0 @ X10 @ (k1_relat_1 @ X11))
% 0.44/0.71          | ((k7_relat_1 @ X11 @ X10) = (k1_xboole_0))
% 0.44/0.71          | ~ (v1_relat_1 @ X11))),
% 0.44/0.71      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.71  thf('132', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.71          | ~ (v1_relat_1 @ sk_F)
% 0.44/0.71          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['130', '131'])).
% 0.44/0.71  thf('133', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.71      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.71  thf('134', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.71          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.71      inference('demod', [status(thm)], ['132', '133'])).
% 0.44/0.71  thf('135', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['113', '134'])).
% 0.44/0.71  thf('136', plain,
% 0.44/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.71         (((k7_relat_1 @ X7 @ (k3_xboole_0 @ X8 @ X9))
% 0.44/0.71            = (k3_xboole_0 @ (k7_relat_1 @ X7 @ X8) @ (k7_relat_1 @ X7 @ X9)))
% 0.44/0.71          | ~ (v1_relat_1 @ X7))),
% 0.44/0.71      inference('cnf', [status(esa)], [t108_relat_1])).
% 0.44/0.71  thf('137', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ X0))
% 0.44/0.71            = (k3_xboole_0 @ k1_xboole_0 @ (k7_relat_1 @ sk_F @ X0)))
% 0.44/0.71          | ~ (v1_relat_1 @ sk_F))),
% 0.44/0.71      inference('sup+', [status(thm)], ['135', '136'])).
% 0.44/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.71  thf('138', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.44/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.71  thf(t28_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.71  thf('139', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.71  thf('140', plain,
% 0.44/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['138', '139'])).
% 0.44/0.71  thf('141', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.71      inference('sup-', [status(thm)], ['124', '125'])).
% 0.44/0.71  thf('142', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ X0)) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['137', '140', '141'])).
% 0.44/0.71  thf('143', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('144', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('145', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('146', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('147', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71            = (sk_E))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_A))),
% 0.44/0.71      inference('demod', [status(thm)],
% 0.44/0.71                ['48', '49', '50', '51', '52', '55', '60', '100', '101', 
% 0.44/0.71                 '106', '142', '143', '144', '145', '146'])).
% 0.44/0.71  thf('148', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71            = (sk_E))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify', [status(thm)], ['147'])).
% 0.44/0.71  thf('149', plain,
% 0.44/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71            != (sk_E))
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            != (sk_F)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('150', plain,
% 0.44/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71          != (sk_E)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71                = (sk_E))))),
% 0.44/0.71      inference('split', [status(esa)], ['149'])).
% 0.44/0.71  thf('151', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['104', '105'])).
% 0.44/0.71  thf('152', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.71  thf('153', plain,
% 0.44/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.71      inference('split', [status(esa)], ['149'])).
% 0.44/0.71  thf('154', plain,
% 0.44/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['152', '153'])).
% 0.44/0.71  thf('155', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.71  thf('156', plain,
% 0.44/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.44/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.71      inference('demod', [status(thm)], ['154', '155'])).
% 0.44/0.71  thf('157', plain,
% 0.44/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.44/0.71          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['151', '156'])).
% 0.44/0.71  thf('158', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.71  thf('159', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.44/0.71  thf('160', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ X0)) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['137', '140', '141'])).
% 0.44/0.71  thf('161', plain,
% 0.44/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.71      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.44/0.71  thf('162', plain,
% 0.44/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.71      inference('simplify', [status(thm)], ['161'])).
% 0.44/0.71  thf('163', plain,
% 0.44/0.71      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.71  thf('164', plain,
% 0.44/0.71      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.71  thf('165', plain,
% 0.44/0.71      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71         (k1_zfmisc_1 @ 
% 0.44/0.71          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.71  thf('166', plain,
% 0.44/0.71      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X31)
% 0.44/0.71          | (v1_xboole_0 @ X32)
% 0.44/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | ~ (v1_funct_1 @ X34)
% 0.44/0.71          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.44/0.71          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.44/0.71          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 0.44/0.71          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X32)
% 0.44/0.71              = (X34))
% 0.44/0.71          | ~ (m1_subset_1 @ X37 @ 
% 0.44/0.71               (k1_zfmisc_1 @ 
% 0.44/0.71                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 0.44/0.71          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 0.44/0.71          | ~ (v1_funct_1 @ X37)
% 0.44/0.71          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 0.44/0.71              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 0.44/0.71                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 0.44/0.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 0.44/0.71          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 0.44/0.71          | ~ (v1_funct_1 @ X35)
% 0.44/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | (v1_xboole_0 @ X36)
% 0.44/0.71          | (v1_xboole_0 @ X33))),
% 0.44/0.71      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.71  thf('167', plain,
% 0.44/0.71      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.71         ((v1_xboole_0 @ X33)
% 0.44/0.71          | (v1_xboole_0 @ X36)
% 0.44/0.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | ~ (v1_funct_1 @ X35)
% 0.44/0.71          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 0.44/0.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 0.44/0.71          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 0.44/0.71              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 0.44/0.71                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 0.44/0.71          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 0.44/0.71          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 0.44/0.71               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 0.44/0.71          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 0.44/0.71               (k1_zfmisc_1 @ 
% 0.44/0.71                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 0.44/0.71          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 0.44/0.71              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X32) = (
% 0.44/0.71              X34))
% 0.44/0.71          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.44/0.71          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.44/0.71          | ~ (v1_funct_1 @ X34)
% 0.44/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.44/0.71          | (v1_xboole_0 @ X32)
% 0.44/0.71          | (v1_xboole_0 @ X31))),
% 0.44/0.71      inference('simplify', [status(thm)], ['166'])).
% 0.44/0.71  thf('168', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            = (sk_F))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.71            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.71        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.71        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_A))),
% 0.44/0.71      inference('sup-', [status(thm)], ['165', '167'])).
% 0.44/0.71  thf('169', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('170', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('171', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('172', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('173', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.71  thf('174', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.71  thf('175', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.44/0.71  thf('176', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.71  thf('177', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['104', '105'])).
% 0.44/0.71  thf('178', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ X0)) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['137', '140', '141'])).
% 0.44/0.71  thf('179', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('180', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('181', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('182', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('183', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            = (sk_F))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_A))),
% 0.44/0.71      inference('demod', [status(thm)],
% 0.44/0.71                ['168', '169', '170', '171', '172', '173', '174', '175', 
% 0.44/0.71                 '176', '177', '178', '179', '180', '181', '182'])).
% 0.44/0.71  thf('184', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            = (sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify', [status(thm)], ['183'])).
% 0.44/0.71  thf('185', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            = (sk_F))
% 0.44/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['164', '184'])).
% 0.44/0.71  thf('186', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            = (sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify', [status(thm)], ['185'])).
% 0.44/0.71  thf('187', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71            = (sk_F)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['163', '186'])).
% 0.44/0.71  thf('188', plain,
% 0.44/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71          = (sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify', [status(thm)], ['187'])).
% 0.44/0.71  thf('189', plain,
% 0.44/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71          != (sk_F)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71                = (sk_F))))),
% 0.44/0.71      inference('split', [status(esa)], ['149'])).
% 0.44/0.71  thf('190', plain,
% 0.44/0.71      (((((sk_F) != (sk_F))
% 0.44/0.71         | (v1_xboole_0 @ sk_D)
% 0.44/0.71         | (v1_xboole_0 @ sk_C)
% 0.44/0.71         | (v1_xboole_0 @ sk_B)
% 0.44/0.71         | (v1_xboole_0 @ sk_A)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71                = (sk_F))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['188', '189'])).
% 0.44/0.71  thf('191', plain,
% 0.44/0.71      ((((v1_xboole_0 @ sk_A)
% 0.44/0.71         | (v1_xboole_0 @ sk_B)
% 0.44/0.71         | (v1_xboole_0 @ sk_C)
% 0.44/0.71         | (v1_xboole_0 @ sk_D)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71                = (sk_F))))),
% 0.44/0.71      inference('simplify', [status(thm)], ['190'])).
% 0.44/0.71  thf('192', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('193', plain,
% 0.44/0.71      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71                = (sk_F))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['191', '192'])).
% 0.44/0.71  thf('194', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('195', plain,
% 0.44/0.71      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71                = (sk_F))))),
% 0.44/0.71      inference('clc', [status(thm)], ['193', '194'])).
% 0.44/0.71  thf('196', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('197', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_B))
% 0.44/0.71         <= (~
% 0.44/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71                = (sk_F))))),
% 0.44/0.71      inference('clc', [status(thm)], ['195', '196'])).
% 0.44/0.71  thf('198', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('199', plain,
% 0.44/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71          = (sk_F)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['197', '198'])).
% 0.44/0.71  thf('200', plain,
% 0.44/0.71      (~
% 0.44/0.71       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71          = (sk_E))) | 
% 0.44/0.71       ~
% 0.44/0.71       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.71          = (sk_F))) | 
% 0.44/0.71       ~
% 0.44/0.71       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.71          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.71             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.71      inference('split', [status(esa)], ['149'])).
% 0.44/0.71  thf('201', plain,
% 0.44/0.71      (~
% 0.44/0.71       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71          = (sk_E)))),
% 0.44/0.71      inference('sat_resolution*', [status(thm)], ['162', '199', '200'])).
% 0.44/0.71  thf('202', plain,
% 0.44/0.71      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.71         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.71         != (sk_E))),
% 0.44/0.71      inference('simpl_trail', [status(thm)], ['150', '201'])).
% 0.44/0.71  thf('203', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | ~ (v1_funct_2 @ 
% 0.44/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['148', '202'])).
% 0.44/0.71  thf('204', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['30', '203'])).
% 0.44/0.71  thf('205', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify', [status(thm)], ['204'])).
% 0.44/0.71  thf('206', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_D)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_A))),
% 0.44/0.71      inference('sup-', [status(thm)], ['15', '205'])).
% 0.44/0.71  thf('207', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_A)
% 0.44/0.71        | (v1_xboole_0 @ sk_B)
% 0.44/0.71        | (v1_xboole_0 @ sk_C)
% 0.44/0.71        | (v1_xboole_0 @ sk_D))),
% 0.44/0.71      inference('simplify', [status(thm)], ['206'])).
% 0.44/0.71  thf('208', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('209', plain,
% 0.44/0.71      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.44/0.71      inference('sup-', [status(thm)], ['207', '208'])).
% 0.44/0.71  thf('210', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('211', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.71      inference('clc', [status(thm)], ['209', '210'])).
% 0.44/0.71  thf('212', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('213', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.71      inference('clc', [status(thm)], ['211', '212'])).
% 0.44/0.71  thf('214', plain, ($false), inference('demod', [status(thm)], ['0', '213'])).
% 0.44/0.71  
% 0.44/0.71  % SZS output end Refutation
% 0.44/0.71  
% 0.44/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
