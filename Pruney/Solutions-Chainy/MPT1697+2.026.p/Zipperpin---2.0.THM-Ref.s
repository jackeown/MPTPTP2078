%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sjZy6mxfXE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:56 EST 2020

% Result     : Theorem 8.68s
% Output     : Refutation 8.68s
% Verified   : 
% Statistics : Number of formulae       :  267 (1800 expanded)
%              Number of leaves         :   42 ( 543 expanded)
%              Depth                    :   39
%              Number of atoms          : 3734 (69401 expanded)
%              Number of equality atoms :  137 (2279 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_subset_1 @ X14 @ X15 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
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

thf('70',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['76','77'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('79',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('85',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['80','83','86'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k7_relat_1 @ X10 @ ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','91'])).

thf('93',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('94',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('106',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('109',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['103','106','109'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('111',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k7_relat_1 @ X9 @ X8 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','114'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('116',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('117',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_F ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('118',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['103','106','109'])).

thf('120',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('121',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('123',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['80','83','86'])).

thf('126',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k7_relat_1 @ X9 @ X8 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('133',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('134',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('140',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['103','106','109'])).

thf('141',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k7_relat_1 @ X10 @ ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','114'])).

thf('147',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','131','132','133','138','147','148','149','150','151'])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('157',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['154'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('160',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['156','160'])).

thf('162',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('164',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','130'])).

thf('165',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('166',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165'])).

thf('167',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['145','146'])).

thf('168',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('171',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('173',plain,(
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

thf('174',plain,(
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
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
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
    inference('sup-',[status(thm)],['172','174'])).

thf('176',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('181',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('183',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','130'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('185',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('187',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['145','146'])).

thf('188',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
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
    inference(demod,[status(thm)],['175','176','177','178','179','180','181','182','183','184','185','186','187','188','189','190','191'])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
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
    inference('sup-',[status(thm)],['171','193'])).

thf('195',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
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
    inference('sup-',[status(thm)],['170','195'])).

thf('197',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['154'])).

thf('199',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['154'])).

thf('210',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['169','208','209'])).

thf('211',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['155','210'])).

thf('212',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['153','211'])).

thf('213',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','212'])).

thf('214',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    $false ),
    inference(demod,[status(thm)],['0','222'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sjZy6mxfXE
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.68/8.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.68/8.87  % Solved by: fo/fo7.sh
% 8.68/8.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.68/8.87  % done 5096 iterations in 8.410s
% 8.68/8.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.68/8.87  % SZS output start Refutation
% 8.68/8.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.68/8.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 8.68/8.87  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 8.68/8.87  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 8.68/8.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.68/8.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.68/8.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.68/8.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.68/8.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.68/8.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.68/8.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.68/8.87  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 8.68/8.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.68/8.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.68/8.87  thf(sk_F_type, type, sk_F: $i).
% 8.68/8.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.68/8.87  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.68/8.87  thf(sk_E_type, type, sk_E: $i).
% 8.68/8.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.68/8.87  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 8.68/8.87  thf(sk_C_type, type, sk_C: $i).
% 8.68/8.87  thf(sk_D_type, type, sk_D: $i).
% 8.68/8.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.68/8.87  thf(sk_B_type, type, sk_B: $i).
% 8.68/8.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.68/8.87  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.68/8.87  thf(sk_A_type, type, sk_A: $i).
% 8.68/8.87  thf(t6_tmap_1, conjecture,
% 8.68/8.87    (![A:$i]:
% 8.68/8.87     ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.68/8.87       ( ![B:$i]:
% 8.68/8.87         ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.68/8.87           ( ![C:$i]:
% 8.68/8.87             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 8.68/8.87                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.68/8.87               ( ![D:$i]:
% 8.68/8.87                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 8.68/8.87                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.68/8.87                   ( ( r1_subset_1 @ C @ D ) =>
% 8.68/8.87                     ( ![E:$i]:
% 8.68/8.87                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 8.68/8.87                           ( m1_subset_1 @
% 8.68/8.87                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 8.68/8.87                         ( ![F:$i]:
% 8.68/8.87                           ( ( ( v1_funct_1 @ F ) & 
% 8.68/8.87                               ( v1_funct_2 @ F @ D @ B ) & 
% 8.68/8.87                               ( m1_subset_1 @
% 8.68/8.87                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 8.68/8.87                             ( ( ( k2_partfun1 @
% 8.68/8.87                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 8.68/8.87                                 ( k2_partfun1 @
% 8.68/8.87                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 8.68/8.87                               ( ( k2_partfun1 @
% 8.68/8.87                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 8.68/8.87                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 8.68/8.87                                 ( E ) ) & 
% 8.68/8.87                               ( ( k2_partfun1 @
% 8.68/8.87                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 8.68/8.87                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 8.68/8.87                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.68/8.87  thf(zf_stmt_0, negated_conjecture,
% 8.68/8.87    (~( ![A:$i]:
% 8.68/8.87        ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.68/8.87          ( ![B:$i]:
% 8.68/8.87            ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.68/8.87              ( ![C:$i]:
% 8.68/8.87                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 8.68/8.87                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.68/8.87                  ( ![D:$i]:
% 8.68/8.87                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 8.68/8.87                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.68/8.87                      ( ( r1_subset_1 @ C @ D ) =>
% 8.68/8.87                        ( ![E:$i]:
% 8.68/8.87                          ( ( ( v1_funct_1 @ E ) & 
% 8.68/8.87                              ( v1_funct_2 @ E @ C @ B ) & 
% 8.68/8.87                              ( m1_subset_1 @
% 8.68/8.87                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 8.68/8.87                            ( ![F:$i]:
% 8.68/8.87                              ( ( ( v1_funct_1 @ F ) & 
% 8.68/8.87                                  ( v1_funct_2 @ F @ D @ B ) & 
% 8.68/8.87                                  ( m1_subset_1 @
% 8.68/8.87                                    F @ 
% 8.68/8.87                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 8.68/8.87                                ( ( ( k2_partfun1 @
% 8.68/8.87                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 8.68/8.87                                    ( k2_partfun1 @
% 8.68/8.87                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 8.68/8.87                                  ( ( k2_partfun1 @
% 8.68/8.87                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 8.68/8.87                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 8.68/8.87                                    ( E ) ) & 
% 8.68/8.87                                  ( ( k2_partfun1 @
% 8.68/8.87                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 8.68/8.87                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 8.68/8.87                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 8.68/8.87    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 8.68/8.87  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('2', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('3', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(dt_k1_tmap_1, axiom,
% 8.68/8.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.68/8.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 8.68/8.87         ( ~( v1_xboole_0 @ C ) ) & 
% 8.68/8.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 8.68/8.87         ( ~( v1_xboole_0 @ D ) ) & 
% 8.68/8.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 8.68/8.87         ( v1_funct_2 @ E @ C @ B ) & 
% 8.68/8.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 8.68/8.87         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 8.68/8.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 8.68/8.87       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 8.68/8.87         ( v1_funct_2 @
% 8.68/8.87           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.68/8.87           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 8.68/8.87         ( m1_subset_1 @
% 8.68/8.87           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.68/8.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 8.68/8.87  thf('4', plain,
% 8.68/8.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 8.68/8.87          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 8.68/8.87          | ~ (v1_funct_1 @ X38)
% 8.68/8.87          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 8.68/8.87          | (v1_xboole_0 @ X41)
% 8.68/8.87          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 8.68/8.87          | (v1_xboole_0 @ X39)
% 8.68/8.87          | (v1_xboole_0 @ X40)
% 8.68/8.87          | (v1_xboole_0 @ X42)
% 8.68/8.87          | ~ (v1_funct_1 @ X43)
% 8.68/8.87          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 8.68/8.87          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 8.68/8.87          | (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43)))),
% 8.68/8.87      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 8.68/8.87  thf('5', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.68/8.87         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 8.68/8.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.68/8.87          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.68/8.87          | ~ (v1_funct_1 @ X0)
% 8.68/8.87          | (v1_xboole_0 @ X2)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 8.68/8.87          | (v1_xboole_0 @ X1)
% 8.68/8.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 8.68/8.87          | ~ (v1_funct_1 @ sk_E)
% 8.68/8.87          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 8.68/8.87      inference('sup-', [status(thm)], ['3', '4'])).
% 8.68/8.87  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('8', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.68/8.87         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 8.68/8.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.68/8.87          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.68/8.87          | ~ (v1_funct_1 @ X0)
% 8.68/8.87          | (v1_xboole_0 @ X2)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 8.68/8.87          | (v1_xboole_0 @ X1)
% 8.68/8.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 8.68/8.87      inference('demod', [status(thm)], ['5', '6', '7'])).
% 8.68/8.87  thf('9', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_D)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (v1_funct_1 @ sk_F)
% 8.68/8.87          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 8.68/8.87          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['2', '8'])).
% 8.68/8.87  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('12', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_D)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 8.68/8.87      inference('demod', [status(thm)], ['9', '10', '11'])).
% 8.68/8.87  thf('13', plain,
% 8.68/8.87      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['1', '12'])).
% 8.68/8.87  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('15', plain,
% 8.68/8.87      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['13', '14'])).
% 8.68/8.87  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('17', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('18', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('19', plain,
% 8.68/8.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 8.68/8.87          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 8.68/8.87          | ~ (v1_funct_1 @ X38)
% 8.68/8.87          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 8.68/8.87          | (v1_xboole_0 @ X41)
% 8.68/8.87          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 8.68/8.87          | (v1_xboole_0 @ X39)
% 8.68/8.87          | (v1_xboole_0 @ X40)
% 8.68/8.87          | (v1_xboole_0 @ X42)
% 8.68/8.87          | ~ (v1_funct_1 @ X43)
% 8.68/8.87          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 8.68/8.87          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 8.68/8.87          | (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 8.68/8.87             (k4_subset_1 @ X42 @ X39 @ X41) @ X40))),
% 8.68/8.87      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 8.68/8.87  thf('20', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.68/8.87         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 8.68/8.87           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 8.68/8.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 8.68/8.87          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 8.68/8.87          | ~ (v1_funct_1 @ X2)
% 8.68/8.87          | (v1_xboole_0 @ X1)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 8.68/8.87          | ~ (v1_funct_1 @ sk_E)
% 8.68/8.87          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 8.68/8.87      inference('sup-', [status(thm)], ['18', '19'])).
% 8.68/8.87  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('23', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.68/8.87         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 8.68/8.87           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 8.68/8.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 8.68/8.87          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 8.68/8.87          | ~ (v1_funct_1 @ X2)
% 8.68/8.87          | (v1_xboole_0 @ X1)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 8.68/8.87      inference('demod', [status(thm)], ['20', '21', '22'])).
% 8.68/8.87  thf('24', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_D)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (v1_funct_1 @ sk_F)
% 8.68/8.87          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 8.68/8.87          | (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 8.68/8.87      inference('sup-', [status(thm)], ['17', '23'])).
% 8.68/8.87  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('27', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_D)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 8.68/8.87      inference('demod', [status(thm)], ['24', '25', '26'])).
% 8.68/8.87  thf('28', plain,
% 8.68/8.87      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['16', '27'])).
% 8.68/8.87  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('30', plain,
% 8.68/8.87      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['28', '29'])).
% 8.68/8.87  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('32', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('33', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('34', plain,
% 8.68/8.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 8.68/8.87          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 8.68/8.87          | ~ (v1_funct_1 @ X38)
% 8.68/8.87          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 8.68/8.87          | (v1_xboole_0 @ X41)
% 8.68/8.87          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 8.68/8.87          | (v1_xboole_0 @ X39)
% 8.68/8.87          | (v1_xboole_0 @ X40)
% 8.68/8.87          | (v1_xboole_0 @ X42)
% 8.68/8.87          | ~ (v1_funct_1 @ X43)
% 8.68/8.87          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 8.68/8.87          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 8.68/8.87          | (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 8.68/8.87             (k1_zfmisc_1 @ 
% 8.68/8.87              (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X39 @ X41) @ X40))))),
% 8.68/8.87      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 8.68/8.87  thf('35', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.68/8.87         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 8.68/8.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 8.68/8.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 8.68/8.87          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 8.68/8.87          | ~ (v1_funct_1 @ X2)
% 8.68/8.87          | (v1_xboole_0 @ X1)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 8.68/8.87          | ~ (v1_funct_1 @ sk_E)
% 8.68/8.87          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 8.68/8.87      inference('sup-', [status(thm)], ['33', '34'])).
% 8.68/8.87  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('38', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.68/8.87         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 8.68/8.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 8.68/8.87          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 8.68/8.87          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 8.68/8.87          | ~ (v1_funct_1 @ X2)
% 8.68/8.87          | (v1_xboole_0 @ X1)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 8.68/8.87      inference('demod', [status(thm)], ['35', '36', '37'])).
% 8.68/8.87  thf('39', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_D)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | ~ (v1_funct_1 @ sk_F)
% 8.68/8.87          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 8.68/8.87          | (m1_subset_1 @ 
% 8.68/8.87             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k1_zfmisc_1 @ 
% 8.68/8.87              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 8.68/8.87      inference('sup-', [status(thm)], ['32', '38'])).
% 8.68/8.87  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('42', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_D)
% 8.68/8.87          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 8.68/8.87          | (v1_xboole_0 @ sk_C)
% 8.68/8.87          | (v1_xboole_0 @ sk_B)
% 8.68/8.87          | (v1_xboole_0 @ X0)
% 8.68/8.87          | (m1_subset_1 @ 
% 8.68/8.87             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k1_zfmisc_1 @ 
% 8.68/8.87              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 8.68/8.87      inference('demod', [status(thm)], ['39', '40', '41'])).
% 8.68/8.87  thf('43', plain,
% 8.68/8.87      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87         (k1_zfmisc_1 @ 
% 8.68/8.87          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['31', '42'])).
% 8.68/8.87  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('45', plain,
% 8.68/8.87      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87         (k1_zfmisc_1 @ 
% 8.68/8.87          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['43', '44'])).
% 8.68/8.87  thf(d1_tmap_1, axiom,
% 8.68/8.87    (![A:$i]:
% 8.68/8.87     ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.68/8.87       ( ![B:$i]:
% 8.68/8.87         ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.68/8.87           ( ![C:$i]:
% 8.68/8.87             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 8.68/8.87                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.68/8.87               ( ![D:$i]:
% 8.68/8.87                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 8.68/8.87                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.68/8.87                   ( ![E:$i]:
% 8.68/8.87                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 8.68/8.87                         ( m1_subset_1 @
% 8.68/8.87                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 8.68/8.87                       ( ![F:$i]:
% 8.68/8.87                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 8.68/8.87                             ( m1_subset_1 @
% 8.68/8.87                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 8.68/8.87                           ( ( ( k2_partfun1 @
% 8.68/8.87                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 8.68/8.87                               ( k2_partfun1 @
% 8.68/8.87                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 8.68/8.87                             ( ![G:$i]:
% 8.68/8.87                               ( ( ( v1_funct_1 @ G ) & 
% 8.68/8.87                                   ( v1_funct_2 @
% 8.68/8.87                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 8.68/8.87                                   ( m1_subset_1 @
% 8.68/8.87                                     G @ 
% 8.68/8.87                                     ( k1_zfmisc_1 @
% 8.68/8.87                                       ( k2_zfmisc_1 @
% 8.68/8.87                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 8.68/8.87                                 ( ( ( G ) =
% 8.68/8.87                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 8.68/8.87                                   ( ( ( k2_partfun1 @
% 8.68/8.87                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 8.68/8.87                                         C ) =
% 8.68/8.87                                       ( E ) ) & 
% 8.68/8.87                                     ( ( k2_partfun1 @
% 8.68/8.87                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 8.68/8.87                                         D ) =
% 8.68/8.87                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.68/8.87  thf('46', plain,
% 8.68/8.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 8.68/8.87         ((v1_xboole_0 @ X31)
% 8.68/8.87          | (v1_xboole_0 @ X32)
% 8.68/8.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | ~ (v1_funct_1 @ X34)
% 8.68/8.87          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 8.68/8.87          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 8.68/8.87          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 8.68/8.87          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X36)
% 8.68/8.87              = (X35))
% 8.68/8.87          | ~ (m1_subset_1 @ X37 @ 
% 8.68/8.87               (k1_zfmisc_1 @ 
% 8.68/8.87                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 8.68/8.87          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 8.68/8.87          | ~ (v1_funct_1 @ X37)
% 8.68/8.87          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 8.68/8.87              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 8.68/8.87                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 8.68/8.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 8.68/8.87          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 8.68/8.87          | ~ (v1_funct_1 @ X35)
% 8.68/8.87          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | (v1_xboole_0 @ X36)
% 8.68/8.87          | (v1_xboole_0 @ X33))),
% 8.68/8.87      inference('cnf', [status(esa)], [d1_tmap_1])).
% 8.68/8.87  thf('47', plain,
% 8.68/8.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 8.68/8.87         ((v1_xboole_0 @ X33)
% 8.68/8.87          | (v1_xboole_0 @ X36)
% 8.68/8.87          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | ~ (v1_funct_1 @ X35)
% 8.68/8.87          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 8.68/8.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 8.68/8.87          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 8.68/8.87              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 8.68/8.87                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 8.68/8.87          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 8.68/8.87          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 8.68/8.87               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 8.68/8.87          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 8.68/8.87               (k1_zfmisc_1 @ 
% 8.68/8.87                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 8.68/8.87          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 8.68/8.87              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X36) = (
% 8.68/8.87              X35))
% 8.68/8.87          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 8.68/8.87          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 8.68/8.87          | ~ (v1_funct_1 @ X34)
% 8.68/8.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | (v1_xboole_0 @ X32)
% 8.68/8.87          | (v1_xboole_0 @ X31))),
% 8.68/8.87      inference('simplify', [status(thm)], ['46'])).
% 8.68/8.87  thf('48', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | ~ (v1_funct_1 @ sk_F)
% 8.68/8.87        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87            = (sk_E))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 8.68/8.87        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 8.68/8.87        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ sk_E)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_A))),
% 8.68/8.87      inference('sup-', [status(thm)], ['45', '47'])).
% 8.68/8.87  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('52', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(redefinition_k9_subset_1, axiom,
% 8.68/8.87    (![A:$i,B:$i,C:$i]:
% 8.68/8.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.68/8.87       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 8.68/8.87  thf('54', plain,
% 8.68/8.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.68/8.87         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 8.68/8.87          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 8.68/8.87      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 8.68/8.87  thf('55', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['53', '54'])).
% 8.68/8.87  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(redefinition_r1_subset_1, axiom,
% 8.68/8.87    (![A:$i,B:$i]:
% 8.68/8.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 8.68/8.87       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 8.68/8.87  thf('57', plain,
% 8.68/8.87      (![X14 : $i, X15 : $i]:
% 8.68/8.87         ((v1_xboole_0 @ X14)
% 8.68/8.87          | (v1_xboole_0 @ X15)
% 8.68/8.87          | (r1_xboole_0 @ X14 @ X15)
% 8.68/8.87          | ~ (r1_subset_1 @ X14 @ X15))),
% 8.68/8.87      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 8.68/8.87  thf('58', plain,
% 8.68/8.87      (((r1_xboole_0 @ sk_C @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C))),
% 8.68/8.87      inference('sup-', [status(thm)], ['56', '57'])).
% 8.68/8.87  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 8.68/8.87      inference('clc', [status(thm)], ['58', '59'])).
% 8.68/8.87  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 8.68/8.87      inference('clc', [status(thm)], ['60', '61'])).
% 8.68/8.87  thf(d7_xboole_0, axiom,
% 8.68/8.87    (![A:$i,B:$i]:
% 8.68/8.87     ( ( r1_xboole_0 @ A @ B ) <=>
% 8.68/8.87       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 8.68/8.87  thf('63', plain,
% 8.68/8.87      (![X0 : $i, X1 : $i]:
% 8.68/8.87         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 8.68/8.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 8.68/8.87  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('65', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(redefinition_k2_partfun1, axiom,
% 8.68/8.87    (![A:$i,B:$i,C:$i,D:$i]:
% 8.68/8.87     ( ( ( v1_funct_1 @ C ) & 
% 8.68/8.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.68/8.87       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 8.68/8.87  thf('66', plain,
% 8.68/8.87      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 8.68/8.87          | ~ (v1_funct_1 @ X27)
% 8.68/8.87          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 8.68/8.87      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 8.68/8.87  thf('67', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 8.68/8.87          | ~ (v1_funct_1 @ sk_E))),
% 8.68/8.87      inference('sup-', [status(thm)], ['65', '66'])).
% 8.68/8.87  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('69', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 8.68/8.87      inference('demod', [status(thm)], ['67', '68'])).
% 8.68/8.87  thf('70', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('71', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(cc5_funct_2, axiom,
% 8.68/8.87    (![A:$i,B:$i]:
% 8.68/8.87     ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.68/8.87       ( ![C:$i]:
% 8.68/8.87         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.68/8.87           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 8.68/8.87             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 8.68/8.87  thf('72', plain,
% 8.68/8.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 8.68/8.87          | (v1_partfun1 @ X22 @ X23)
% 8.68/8.87          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 8.68/8.87          | ~ (v1_funct_1 @ X22)
% 8.68/8.87          | (v1_xboole_0 @ X24))),
% 8.68/8.87      inference('cnf', [status(esa)], [cc5_funct_2])).
% 8.68/8.87  thf('73', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ sk_E)
% 8.68/8.87        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 8.68/8.87        | (v1_partfun1 @ sk_E @ sk_C))),
% 8.68/8.87      inference('sup-', [status(thm)], ['71', '72'])).
% 8.68/8.87  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('75', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('76', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 8.68/8.87      inference('demod', [status(thm)], ['73', '74', '75'])).
% 8.68/8.87  thf('77', plain, (~ (v1_xboole_0 @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('78', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 8.68/8.87      inference('clc', [status(thm)], ['76', '77'])).
% 8.68/8.87  thf(d4_partfun1, axiom,
% 8.68/8.87    (![A:$i,B:$i]:
% 8.68/8.87     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 8.68/8.87       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 8.68/8.87  thf('79', plain,
% 8.68/8.87      (![X25 : $i, X26 : $i]:
% 8.68/8.87         (~ (v1_partfun1 @ X26 @ X25)
% 8.68/8.87          | ((k1_relat_1 @ X26) = (X25))
% 8.68/8.87          | ~ (v4_relat_1 @ X26 @ X25)
% 8.68/8.87          | ~ (v1_relat_1 @ X26))),
% 8.68/8.87      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.68/8.87  thf('80', plain,
% 8.68/8.87      ((~ (v1_relat_1 @ sk_E)
% 8.68/8.87        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 8.68/8.87        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['78', '79'])).
% 8.68/8.87  thf('81', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(cc1_relset_1, axiom,
% 8.68/8.87    (![A:$i,B:$i,C:$i]:
% 8.68/8.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.68/8.87       ( v1_relat_1 @ C ) ))).
% 8.68/8.87  thf('82', plain,
% 8.68/8.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.68/8.87         ((v1_relat_1 @ X16)
% 8.68/8.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 8.68/8.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.68/8.87  thf('83', plain, ((v1_relat_1 @ sk_E)),
% 8.68/8.87      inference('sup-', [status(thm)], ['81', '82'])).
% 8.68/8.87  thf('84', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf(cc2_relset_1, axiom,
% 8.68/8.87    (![A:$i,B:$i,C:$i]:
% 8.68/8.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.68/8.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.68/8.87  thf('85', plain,
% 8.68/8.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.68/8.87         ((v4_relat_1 @ X19 @ X20)
% 8.68/8.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 8.68/8.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.68/8.87  thf('86', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 8.68/8.87      inference('sup-', [status(thm)], ['84', '85'])).
% 8.68/8.87  thf('87', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 8.68/8.87      inference('demod', [status(thm)], ['80', '83', '86'])).
% 8.68/8.87  thf(t192_relat_1, axiom,
% 8.68/8.87    (![A:$i,B:$i]:
% 8.68/8.87     ( ( v1_relat_1 @ B ) =>
% 8.68/8.87       ( ( k7_relat_1 @ B @ A ) =
% 8.68/8.87         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 8.68/8.87  thf('88', plain,
% 8.68/8.87      (![X10 : $i, X11 : $i]:
% 8.68/8.87         (((k7_relat_1 @ X10 @ X11)
% 8.68/8.87            = (k7_relat_1 @ X10 @ (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11)))
% 8.68/8.87          | ~ (v1_relat_1 @ X10))),
% 8.68/8.87      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.68/8.87  thf('89', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (((k7_relat_1 @ sk_E @ X0)
% 8.68/8.87            = (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C @ X0)))
% 8.68/8.87          | ~ (v1_relat_1 @ sk_E))),
% 8.68/8.87      inference('sup+', [status(thm)], ['87', '88'])).
% 8.68/8.87  thf('90', plain, ((v1_relat_1 @ sk_E)),
% 8.68/8.87      inference('sup-', [status(thm)], ['81', '82'])).
% 8.68/8.87  thf('91', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k7_relat_1 @ sk_E @ X0)
% 8.68/8.87           = (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C @ X0)))),
% 8.68/8.87      inference('demod', [status(thm)], ['89', '90'])).
% 8.68/8.87  thf('92', plain,
% 8.68/8.87      (((k7_relat_1 @ sk_E @ sk_D) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['70', '91'])).
% 8.68/8.87  thf('93', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 8.68/8.87      inference('clc', [status(thm)], ['60', '61'])).
% 8.68/8.87  thf('94', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('95', plain,
% 8.68/8.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 8.68/8.87          | (v1_partfun1 @ X22 @ X23)
% 8.68/8.87          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 8.68/8.87          | ~ (v1_funct_1 @ X22)
% 8.68/8.87          | (v1_xboole_0 @ X24))),
% 8.68/8.87      inference('cnf', [status(esa)], [cc5_funct_2])).
% 8.68/8.87  thf('96', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ sk_F)
% 8.68/8.87        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 8.68/8.87        | (v1_partfun1 @ sk_F @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['94', '95'])).
% 8.68/8.87  thf('97', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('98', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('99', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['96', '97', '98'])).
% 8.68/8.87  thf('100', plain, (~ (v1_xboole_0 @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('101', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 8.68/8.87      inference('clc', [status(thm)], ['99', '100'])).
% 8.68/8.87  thf('102', plain,
% 8.68/8.87      (![X25 : $i, X26 : $i]:
% 8.68/8.87         (~ (v1_partfun1 @ X26 @ X25)
% 8.68/8.87          | ((k1_relat_1 @ X26) = (X25))
% 8.68/8.87          | ~ (v4_relat_1 @ X26 @ X25)
% 8.68/8.87          | ~ (v1_relat_1 @ X26))),
% 8.68/8.87      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.68/8.87  thf('103', plain,
% 8.68/8.87      ((~ (v1_relat_1 @ sk_F)
% 8.68/8.87        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 8.68/8.87        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['101', '102'])).
% 8.68/8.87  thf('104', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('105', plain,
% 8.68/8.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.68/8.87         ((v1_relat_1 @ X16)
% 8.68/8.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 8.68/8.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.68/8.87  thf('106', plain, ((v1_relat_1 @ sk_F)),
% 8.68/8.87      inference('sup-', [status(thm)], ['104', '105'])).
% 8.68/8.87  thf('107', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('108', plain,
% 8.68/8.87      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.68/8.87         ((v4_relat_1 @ X19 @ X20)
% 8.68/8.87          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 8.68/8.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.68/8.87  thf('109', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 8.68/8.87      inference('sup-', [status(thm)], ['107', '108'])).
% 8.68/8.87  thf('110', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['103', '106', '109'])).
% 8.68/8.87  thf(t187_relat_1, axiom,
% 8.68/8.87    (![A:$i]:
% 8.68/8.87     ( ( v1_relat_1 @ A ) =>
% 8.68/8.87       ( ![B:$i]:
% 8.68/8.87         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 8.68/8.87           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 8.68/8.87  thf('111', plain,
% 8.68/8.87      (![X8 : $i, X9 : $i]:
% 8.68/8.87         (~ (r1_xboole_0 @ X8 @ (k1_relat_1 @ X9))
% 8.68/8.87          | ((k7_relat_1 @ X9 @ X8) = (k1_xboole_0))
% 8.68/8.87          | ~ (v1_relat_1 @ X9))),
% 8.68/8.87      inference('cnf', [status(esa)], [t187_relat_1])).
% 8.68/8.87  thf('112', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (r1_xboole_0 @ X0 @ sk_D)
% 8.68/8.87          | ~ (v1_relat_1 @ sk_F)
% 8.68/8.87          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['110', '111'])).
% 8.68/8.87  thf('113', plain, ((v1_relat_1 @ sk_F)),
% 8.68/8.87      inference('sup-', [status(thm)], ['104', '105'])).
% 8.68/8.87  thf('114', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (r1_xboole_0 @ X0 @ sk_D)
% 8.68/8.87          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 8.68/8.87      inference('demod', [status(thm)], ['112', '113'])).
% 8.68/8.87  thf('115', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['93', '114'])).
% 8.68/8.87  thf(t90_relat_1, axiom,
% 8.68/8.87    (![A:$i,B:$i]:
% 8.68/8.87     ( ( v1_relat_1 @ B ) =>
% 8.68/8.87       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 8.68/8.87         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.68/8.87  thf('116', plain,
% 8.68/8.87      (![X12 : $i, X13 : $i]:
% 8.68/8.87         (((k1_relat_1 @ (k7_relat_1 @ X12 @ X13))
% 8.68/8.87            = (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13))
% 8.68/8.87          | ~ (v1_relat_1 @ X12))),
% 8.68/8.87      inference('cnf', [status(esa)], [t90_relat_1])).
% 8.68/8.87  thf('117', plain,
% 8.68/8.87      ((((k1_relat_1 @ k1_xboole_0)
% 8.68/8.87          = (k3_xboole_0 @ (k1_relat_1 @ sk_F) @ sk_C))
% 8.68/8.87        | ~ (v1_relat_1 @ sk_F))),
% 8.68/8.87      inference('sup+', [status(thm)], ['115', '116'])).
% 8.68/8.87  thf(t60_relat_1, axiom,
% 8.68/8.87    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 8.68/8.87     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 8.68/8.87  thf('118', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('cnf', [status(esa)], [t60_relat_1])).
% 8.68/8.87  thf('119', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['103', '106', '109'])).
% 8.68/8.87  thf('120', plain, ((v1_relat_1 @ sk_F)),
% 8.68/8.87      inference('sup-', [status(thm)], ['104', '105'])).
% 8.68/8.87  thf('121', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 8.68/8.87      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 8.68/8.87  thf('122', plain,
% 8.68/8.87      (![X0 : $i, X2 : $i]:
% 8.68/8.87         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 8.68/8.87      inference('cnf', [status(esa)], [d7_xboole_0])).
% 8.68/8.87  thf('123', plain,
% 8.68/8.87      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_D @ sk_C))),
% 8.68/8.87      inference('sup-', [status(thm)], ['121', '122'])).
% 8.68/8.87  thf('124', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 8.68/8.87      inference('simplify', [status(thm)], ['123'])).
% 8.68/8.87  thf('125', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 8.68/8.87      inference('demod', [status(thm)], ['80', '83', '86'])).
% 8.68/8.87  thf('126', plain,
% 8.68/8.87      (![X8 : $i, X9 : $i]:
% 8.68/8.87         (~ (r1_xboole_0 @ X8 @ (k1_relat_1 @ X9))
% 8.68/8.87          | ((k7_relat_1 @ X9 @ X8) = (k1_xboole_0))
% 8.68/8.87          | ~ (v1_relat_1 @ X9))),
% 8.68/8.87      inference('cnf', [status(esa)], [t187_relat_1])).
% 8.68/8.87  thf('127', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (r1_xboole_0 @ X0 @ sk_C)
% 8.68/8.87          | ~ (v1_relat_1 @ sk_E)
% 8.68/8.87          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['125', '126'])).
% 8.68/8.87  thf('128', plain, ((v1_relat_1 @ sk_E)),
% 8.68/8.87      inference('sup-', [status(thm)], ['81', '82'])).
% 8.68/8.87  thf('129', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (~ (r1_xboole_0 @ X0 @ sk_C)
% 8.68/8.87          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 8.68/8.87      inference('demod', [status(thm)], ['127', '128'])).
% 8.68/8.87  thf('130', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['124', '129'])).
% 8.68/8.87  thf('131', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['92', '130'])).
% 8.68/8.87  thf('132', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['53', '54'])).
% 8.68/8.87  thf('133', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('134', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('135', plain,
% 8.68/8.87      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.68/8.87         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 8.68/8.87          | ~ (v1_funct_1 @ X27)
% 8.68/8.87          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 8.68/8.87      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 8.68/8.87  thf('136', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 8.68/8.87          | ~ (v1_funct_1 @ sk_F))),
% 8.68/8.87      inference('sup-', [status(thm)], ['134', '135'])).
% 8.68/8.87  thf('137', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('138', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 8.68/8.87      inference('demod', [status(thm)], ['136', '137'])).
% 8.68/8.87  thf('139', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 8.68/8.87      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 8.68/8.87  thf('140', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['103', '106', '109'])).
% 8.68/8.87  thf('141', plain,
% 8.68/8.87      (![X10 : $i, X11 : $i]:
% 8.68/8.87         (((k7_relat_1 @ X10 @ X11)
% 8.68/8.87            = (k7_relat_1 @ X10 @ (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11)))
% 8.68/8.87          | ~ (v1_relat_1 @ X10))),
% 8.68/8.87      inference('cnf', [status(esa)], [t192_relat_1])).
% 8.68/8.87  thf('142', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         (((k7_relat_1 @ sk_F @ X0)
% 8.68/8.87            = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_D @ X0)))
% 8.68/8.87          | ~ (v1_relat_1 @ sk_F))),
% 8.68/8.87      inference('sup+', [status(thm)], ['140', '141'])).
% 8.68/8.87  thf('143', plain, ((v1_relat_1 @ sk_F)),
% 8.68/8.87      inference('sup-', [status(thm)], ['104', '105'])).
% 8.68/8.87  thf('144', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k7_relat_1 @ sk_F @ X0)
% 8.68/8.87           = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_D @ X0)))),
% 8.68/8.87      inference('demod', [status(thm)], ['142', '143'])).
% 8.68/8.87  thf('145', plain,
% 8.68/8.87      (((k7_relat_1 @ sk_F @ sk_C) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['139', '144'])).
% 8.68/8.87  thf('146', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['93', '114'])).
% 8.68/8.87  thf('147', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['145', '146'])).
% 8.68/8.87  thf('148', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('149', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('150', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('151', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('152', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87            = (sk_E))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ((k1_xboole_0) != (k1_xboole_0))
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_A))),
% 8.68/8.87      inference('demod', [status(thm)],
% 8.68/8.87                ['48', '49', '50', '51', '52', '55', '64', '69', '131', '132', 
% 8.68/8.87                 '133', '138', '147', '148', '149', '150', '151'])).
% 8.68/8.87  thf('153', plain,
% 8.68/8.87      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87            = (sk_E))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify', [status(thm)], ['152'])).
% 8.68/8.87  thf('154', plain,
% 8.68/8.87      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87            != (sk_E))
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            != (sk_F)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('155', plain,
% 8.68/8.87      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87          != (sk_E)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87                = (sk_E))))),
% 8.68/8.87      inference('split', [status(esa)], ['154'])).
% 8.68/8.87  thf('156', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 8.68/8.87      inference('demod', [status(thm)], ['136', '137'])).
% 8.68/8.87  thf('157', plain,
% 8.68/8.87      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 8.68/8.87      inference('split', [status(esa)], ['154'])).
% 8.68/8.87  thf('158', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['53', '54'])).
% 8.68/8.87  thf('159', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['53', '54'])).
% 8.68/8.87  thf('160', plain,
% 8.68/8.87      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 8.68/8.87          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 8.68/8.87      inference('demod', [status(thm)], ['157', '158', '159'])).
% 8.68/8.87  thf('161', plain,
% 8.68/8.87      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 8.68/8.87          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 8.68/8.87      inference('sup-', [status(thm)], ['156', '160'])).
% 8.68/8.87  thf('162', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('163', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 8.68/8.87      inference('demod', [status(thm)], ['67', '68'])).
% 8.68/8.87  thf('164', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['92', '130'])).
% 8.68/8.87  thf('165', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('166', plain,
% 8.68/8.87      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 8.68/8.87      inference('demod', [status(thm)], ['161', '162', '163', '164', '165'])).
% 8.68/8.87  thf('167', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['145', '146'])).
% 8.68/8.87  thf('168', plain,
% 8.68/8.87      ((((k1_xboole_0) != (k1_xboole_0)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 8.68/8.87      inference('demod', [status(thm)], ['166', '167'])).
% 8.68/8.87  thf('169', plain,
% 8.68/8.87      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 8.68/8.87      inference('simplify', [status(thm)], ['168'])).
% 8.68/8.87  thf('170', plain,
% 8.68/8.87      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['13', '14'])).
% 8.68/8.87  thf('171', plain,
% 8.68/8.87      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['28', '29'])).
% 8.68/8.87  thf('172', plain,
% 8.68/8.87      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87         (k1_zfmisc_1 @ 
% 8.68/8.87          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('demod', [status(thm)], ['43', '44'])).
% 8.68/8.87  thf('173', plain,
% 8.68/8.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 8.68/8.87         ((v1_xboole_0 @ X31)
% 8.68/8.87          | (v1_xboole_0 @ X32)
% 8.68/8.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | ~ (v1_funct_1 @ X34)
% 8.68/8.87          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 8.68/8.87          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 8.68/8.87          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 8.68/8.87          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X32)
% 8.68/8.87              = (X34))
% 8.68/8.87          | ~ (m1_subset_1 @ X37 @ 
% 8.68/8.87               (k1_zfmisc_1 @ 
% 8.68/8.87                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 8.68/8.87          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 8.68/8.87          | ~ (v1_funct_1 @ X37)
% 8.68/8.87          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 8.68/8.87              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 8.68/8.87                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 8.68/8.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 8.68/8.87          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 8.68/8.87          | ~ (v1_funct_1 @ X35)
% 8.68/8.87          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | (v1_xboole_0 @ X36)
% 8.68/8.87          | (v1_xboole_0 @ X33))),
% 8.68/8.87      inference('cnf', [status(esa)], [d1_tmap_1])).
% 8.68/8.87  thf('174', plain,
% 8.68/8.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 8.68/8.87         ((v1_xboole_0 @ X33)
% 8.68/8.87          | (v1_xboole_0 @ X36)
% 8.68/8.87          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | ~ (v1_funct_1 @ X35)
% 8.68/8.87          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 8.68/8.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 8.68/8.87          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 8.68/8.87              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 8.68/8.87                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 8.68/8.87          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 8.68/8.87          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 8.68/8.87               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 8.68/8.87          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 8.68/8.87               (k1_zfmisc_1 @ 
% 8.68/8.87                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 8.68/8.87          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 8.68/8.87              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X32) = (
% 8.68/8.87              X34))
% 8.68/8.87          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 8.68/8.87          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 8.68/8.87          | ~ (v1_funct_1 @ X34)
% 8.68/8.87          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 8.68/8.87          | (v1_xboole_0 @ X32)
% 8.68/8.87          | (v1_xboole_0 @ X31))),
% 8.68/8.87      inference('simplify', [status(thm)], ['173'])).
% 8.68/8.87  thf('175', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | ~ (v1_funct_1 @ sk_F)
% 8.68/8.87        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            = (sk_F))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 8.68/8.87            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 8.68/8.87        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 8.68/8.87        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ sk_E)
% 8.68/8.87        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_A))),
% 8.68/8.87      inference('sup-', [status(thm)], ['172', '174'])).
% 8.68/8.87  thf('176', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('177', plain, ((v1_funct_1 @ sk_F)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('178', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('179', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('180', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['53', '54'])).
% 8.68/8.87  thf('181', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('182', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 8.68/8.87      inference('demod', [status(thm)], ['67', '68'])).
% 8.68/8.87  thf('183', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['92', '130'])).
% 8.68/8.87  thf('184', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 8.68/8.87      inference('sup-', [status(thm)], ['53', '54'])).
% 8.68/8.87  thf('185', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 8.68/8.87      inference('sup-', [status(thm)], ['62', '63'])).
% 8.68/8.87  thf('186', plain,
% 8.68/8.87      (![X0 : $i]:
% 8.68/8.87         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 8.68/8.87      inference('demod', [status(thm)], ['136', '137'])).
% 8.68/8.87  thf('187', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 8.68/8.87      inference('sup+', [status(thm)], ['145', '146'])).
% 8.68/8.87  thf('188', plain,
% 8.68/8.87      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('189', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('190', plain, ((v1_funct_1 @ sk_E)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('191', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('192', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            = (sk_F))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ((k1_xboole_0) != (k1_xboole_0))
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_A))),
% 8.68/8.87      inference('demod', [status(thm)],
% 8.68/8.87                ['175', '176', '177', '178', '179', '180', '181', '182', 
% 8.68/8.87                 '183', '184', '185', '186', '187', '188', '189', '190', '191'])).
% 8.68/8.87  thf('193', plain,
% 8.68/8.87      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            = (sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify', [status(thm)], ['192'])).
% 8.68/8.87  thf('194', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            = (sk_F))
% 8.68/8.87        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['171', '193'])).
% 8.68/8.87  thf('195', plain,
% 8.68/8.87      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            = (sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify', [status(thm)], ['194'])).
% 8.68/8.87  thf('196', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87            = (sk_F)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['170', '195'])).
% 8.68/8.87  thf('197', plain,
% 8.68/8.87      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87          = (sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify', [status(thm)], ['196'])).
% 8.68/8.87  thf('198', plain,
% 8.68/8.87      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87          != (sk_F)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87                = (sk_F))))),
% 8.68/8.87      inference('split', [status(esa)], ['154'])).
% 8.68/8.87  thf('199', plain,
% 8.68/8.87      (((((sk_F) != (sk_F))
% 8.68/8.87         | (v1_xboole_0 @ sk_D)
% 8.68/8.87         | (v1_xboole_0 @ sk_C)
% 8.68/8.87         | (v1_xboole_0 @ sk_B)
% 8.68/8.87         | (v1_xboole_0 @ sk_A)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87                = (sk_F))))),
% 8.68/8.87      inference('sup-', [status(thm)], ['197', '198'])).
% 8.68/8.87  thf('200', plain,
% 8.68/8.87      ((((v1_xboole_0 @ sk_A)
% 8.68/8.87         | (v1_xboole_0 @ sk_B)
% 8.68/8.87         | (v1_xboole_0 @ sk_C)
% 8.68/8.87         | (v1_xboole_0 @ sk_D)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87                = (sk_F))))),
% 8.68/8.87      inference('simplify', [status(thm)], ['199'])).
% 8.68/8.87  thf('201', plain, (~ (v1_xboole_0 @ sk_D)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('202', plain,
% 8.68/8.87      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87                = (sk_F))))),
% 8.68/8.87      inference('sup-', [status(thm)], ['200', '201'])).
% 8.68/8.87  thf('203', plain, (~ (v1_xboole_0 @ sk_C)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('204', plain,
% 8.68/8.87      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87                = (sk_F))))),
% 8.68/8.87      inference('clc', [status(thm)], ['202', '203'])).
% 8.68/8.87  thf('205', plain, (~ (v1_xboole_0 @ sk_A)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('206', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_B))
% 8.68/8.87         <= (~
% 8.68/8.87             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87                = (sk_F))))),
% 8.68/8.87      inference('clc', [status(thm)], ['204', '205'])).
% 8.68/8.87  thf('207', plain, (~ (v1_xboole_0 @ sk_B)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('208', plain,
% 8.68/8.87      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87          = (sk_F)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['206', '207'])).
% 8.68/8.87  thf('209', plain,
% 8.68/8.87      (~
% 8.68/8.87       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87          = (sk_E))) | 
% 8.68/8.87       ~
% 8.68/8.87       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 8.68/8.87          = (sk_F))) | 
% 8.68/8.87       ~
% 8.68/8.87       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 8.68/8.87          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 8.68/8.87             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 8.68/8.87      inference('split', [status(esa)], ['154'])).
% 8.68/8.87  thf('210', plain,
% 8.68/8.87      (~
% 8.68/8.87       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87          = (sk_E)))),
% 8.68/8.87      inference('sat_resolution*', [status(thm)], ['169', '208', '209'])).
% 8.68/8.87  thf('211', plain,
% 8.68/8.87      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 8.68/8.87         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 8.68/8.87         != (sk_E))),
% 8.68/8.87      inference('simpl_trail', [status(thm)], ['155', '210'])).
% 8.68/8.87  thf('212', plain,
% 8.68/8.87      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | ~ (v1_funct_2 @ 
% 8.68/8.87             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 8.68/8.87             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify_reflect-', [status(thm)], ['153', '211'])).
% 8.68/8.87  thf('213', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 8.68/8.87      inference('sup-', [status(thm)], ['30', '212'])).
% 8.68/8.87  thf('214', plain,
% 8.68/8.87      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify', [status(thm)], ['213'])).
% 8.68/8.87  thf('215', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_D)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_A))),
% 8.68/8.87      inference('sup-', [status(thm)], ['15', '214'])).
% 8.68/8.87  thf('216', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_A)
% 8.68/8.87        | (v1_xboole_0 @ sk_B)
% 8.68/8.87        | (v1_xboole_0 @ sk_C)
% 8.68/8.87        | (v1_xboole_0 @ sk_D))),
% 8.68/8.87      inference('simplify', [status(thm)], ['215'])).
% 8.68/8.87  thf('217', plain, (~ (v1_xboole_0 @ sk_D)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('218', plain,
% 8.68/8.87      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 8.68/8.87      inference('sup-', [status(thm)], ['216', '217'])).
% 8.68/8.87  thf('219', plain, (~ (v1_xboole_0 @ sk_C)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('220', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 8.68/8.87      inference('clc', [status(thm)], ['218', '219'])).
% 8.68/8.87  thf('221', plain, (~ (v1_xboole_0 @ sk_A)),
% 8.68/8.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.68/8.87  thf('222', plain, ((v1_xboole_0 @ sk_B)),
% 8.68/8.87      inference('clc', [status(thm)], ['220', '221'])).
% 8.68/8.87  thf('223', plain, ($false), inference('demod', [status(thm)], ['0', '222'])).
% 8.68/8.87  
% 8.68/8.87  % SZS output end Refutation
% 8.68/8.87  
% 8.68/8.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
