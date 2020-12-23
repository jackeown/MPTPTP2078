%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RTbgzBkZU2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:01 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  265 ( 897 expanded)
%              Number of leaves         :   43 ( 283 expanded)
%              Depth                    :   31
%              Number of atoms          : 3800 (33315 expanded)
%              Number of equality atoms :  133 (1101 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_subset_1 @ X16 @ X17 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['90','91'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('93',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('97',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('100',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['94','97','100'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['95','96'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('108',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('109',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X30 @ X31 @ X29 @ X32 )
        = ( k7_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('115',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('127',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('130',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['124','127','130'])).

thf('132',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['125','126'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','106','107','108','113','136','137','138','139','140'])).

thf('142',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
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
    inference('sup-',[status(thm)],['30','142'])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('148',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k7_relat_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

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
    inference(split,[status(esa)],['145'])).

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

thf('158',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('160',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('161',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['150','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['125','126'])).

thf('164',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['149','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['95','96'])).

thf('167',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('170',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('171',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('172',plain,(
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

thf('173',plain,(
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
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
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
    inference('sup-',[status(thm)],['171','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('180',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('182',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','105'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('184',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('186',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','135'])).

thf('187',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
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
    inference(demod,[status(thm)],['174','175','176','177','178','179','180','181','182','183','184','185','186','187','188','189','190'])).

thf('192',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
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
    inference('sup-',[status(thm)],['170','192'])).

thf('194',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
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
    inference('sup-',[status(thm)],['169','194'])).

thf('196',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['145'])).

thf('198',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['145'])).

thf('209',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['168','207','208'])).

thf('210',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['146','209'])).

thf('211',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['144','210'])).

thf('212',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','211'])).

thf('213',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    $false ),
    inference(demod,[status(thm)],['0','219'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RTbgzBkZU2
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:41:10 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 240 iterations in 0.203s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.65  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(t6_tmap_1, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65               ( ![D:$i]:
% 0.46/0.65                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.65                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65                   ( ( r1_subset_1 @ C @ D ) =>
% 0.46/0.65                     ( ![E:$i]:
% 0.46/0.65                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.65                           ( m1_subset_1 @
% 0.46/0.65                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.46/0.65                         ( ![F:$i]:
% 0.46/0.65                           ( ( ( v1_funct_1 @ F ) & 
% 0.46/0.65                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.65                               ( m1_subset_1 @
% 0.46/0.65                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.65                             ( ( ( k2_partfun1 @
% 0.46/0.65                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.46/0.65                                 ( k2_partfun1 @
% 0.46/0.65                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.46/0.65                               ( ( k2_partfun1 @
% 0.46/0.65                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.65                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.46/0.65                                 ( E ) ) & 
% 0.46/0.65                               ( ( k2_partfun1 @
% 0.46/0.65                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.65                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.46/0.65                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65                  ( ![D:$i]:
% 0.46/0.65                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.65                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65                      ( ( r1_subset_1 @ C @ D ) =>
% 0.46/0.65                        ( ![E:$i]:
% 0.46/0.65                          ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.65                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.65                              ( m1_subset_1 @
% 0.46/0.65                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.46/0.65                            ( ![F:$i]:
% 0.46/0.65                              ( ( ( v1_funct_1 @ F ) & 
% 0.46/0.65                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.65                                  ( m1_subset_1 @
% 0.46/0.65                                    F @ 
% 0.46/0.65                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.65                                ( ( ( k2_partfun1 @
% 0.46/0.65                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.46/0.65                                    ( k2_partfun1 @
% 0.46/0.65                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.46/0.65                                  ( ( k2_partfun1 @
% 0.46/0.65                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.65                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.46/0.65                                    ( E ) ) & 
% 0.46/0.65                                  ( ( k2_partfun1 @
% 0.46/0.65                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.65                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.46/0.65                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.46/0.65  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_k1_tmap_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.46/0.65         ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.46/0.65         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.65       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.65         ( v1_funct_2 @
% 0.46/0.65           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.65           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.46/0.65         ( m1_subset_1 @
% 0.46/0.65           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.65           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.65          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.46/0.65          | ~ (v1_funct_1 @ X40)
% 0.46/0.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.46/0.65          | (v1_xboole_0 @ X43)
% 0.46/0.65          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X44))
% 0.46/0.65          | (v1_xboole_0 @ X41)
% 0.46/0.65          | (v1_xboole_0 @ X42)
% 0.46/0.65          | (v1_xboole_0 @ X44)
% 0.46/0.65          | ~ (v1_funct_1 @ X45)
% 0.46/0.65          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.46/0.65          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.46/0.65          | (v1_funct_1 @ (k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ X2)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.46/0.65          | (v1_xboole_0 @ X1)
% 0.46/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.46/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ X2)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.46/0.65          | (v1_xboole_0 @ X1)
% 0.46/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_D)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_F)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.46/0.65          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '8'])).
% 0.46/0.65  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_D)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '12'])).
% 0.46/0.65  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.65          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.46/0.65          | ~ (v1_funct_1 @ X40)
% 0.46/0.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.46/0.65          | (v1_xboole_0 @ X43)
% 0.46/0.65          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X44))
% 0.46/0.65          | (v1_xboole_0 @ X41)
% 0.46/0.65          | (v1_xboole_0 @ X42)
% 0.46/0.65          | (v1_xboole_0 @ X44)
% 0.46/0.65          | ~ (v1_funct_1 @ X45)
% 0.46/0.65          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.46/0.65          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.46/0.65          | (v1_funct_2 @ (k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45) @ 
% 0.46/0.65             (k4_subset_1 @ X44 @ X41 @ X43) @ X42))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.46/0.65           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.46/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_1 @ X2)
% 0.46/0.65          | (v1_xboole_0 @ X1)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.46/0.65           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.46/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_1 @ X2)
% 0.46/0.65          | (v1_xboole_0 @ X1)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_D)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_F)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.46/0.65          | (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '23'])).
% 0.46/0.65  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_D)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '27'])).
% 0.46/0.65  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.65          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.46/0.65          | ~ (v1_funct_1 @ X40)
% 0.46/0.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.46/0.65          | (v1_xboole_0 @ X43)
% 0.46/0.65          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X44))
% 0.46/0.65          | (v1_xboole_0 @ X41)
% 0.46/0.65          | (v1_xboole_0 @ X42)
% 0.46/0.65          | (v1_xboole_0 @ X44)
% 0.46/0.65          | ~ (v1_funct_1 @ X45)
% 0.46/0.65          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.46/0.65          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.46/0.65          | (m1_subset_1 @ (k1_tmap_1 @ X44 @ X42 @ X41 @ X43 @ X40 @ X45) @ 
% 0.46/0.65             (k1_zfmisc_1 @ 
% 0.46/0.65              (k2_zfmisc_1 @ (k4_subset_1 @ X44 @ X41 @ X43) @ X42))))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.46/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_1 @ X2)
% 0.46/0.65          | (v1_xboole_0 @ X1)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.46/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.46/0.65          | ~ (v1_funct_1 @ X2)
% 0.46/0.65          | (v1_xboole_0 @ X1)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_D)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_F)
% 0.46/0.65          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.46/0.65          | (m1_subset_1 @ 
% 0.46/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k1_zfmisc_1 @ 
% 0.46/0.65              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '38'])).
% 0.46/0.65  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_D)
% 0.46/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (v1_xboole_0 @ sk_C)
% 0.46/0.65          | (v1_xboole_0 @ sk_B)
% 0.46/0.65          | (v1_xboole_0 @ X0)
% 0.46/0.65          | (m1_subset_1 @ 
% 0.46/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k1_zfmisc_1 @ 
% 0.46/0.65              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['31', '42'])).
% 0.46/0.65  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf(d1_tmap_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65               ( ![D:$i]:
% 0.46/0.65                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.65                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65                   ( ![E:$i]:
% 0.46/0.65                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.65                         ( m1_subset_1 @
% 0.46/0.65                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.46/0.65                       ( ![F:$i]:
% 0.46/0.65                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.65                             ( m1_subset_1 @
% 0.46/0.65                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.65                           ( ( ( k2_partfun1 @
% 0.46/0.65                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.46/0.65                               ( k2_partfun1 @
% 0.46/0.65                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.46/0.65                             ( ![G:$i]:
% 0.46/0.65                               ( ( ( v1_funct_1 @ G ) & 
% 0.46/0.65                                   ( v1_funct_2 @
% 0.46/0.65                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.46/0.65                                   ( m1_subset_1 @
% 0.46/0.65                                     G @ 
% 0.46/0.65                                     ( k1_zfmisc_1 @
% 0.46/0.65                                       ( k2_zfmisc_1 @
% 0.46/0.65                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.46/0.65                                 ( ( ( G ) =
% 0.46/0.65                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.46/0.65                                   ( ( ( k2_partfun1 @
% 0.46/0.65                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.46/0.65                                         C ) =
% 0.46/0.65                                       ( E ) ) & 
% 0.46/0.65                                     ( ( k2_partfun1 @
% 0.46/0.65                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.46/0.65                                         D ) =
% 0.46/0.65                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X33)
% 0.46/0.65          | (v1_xboole_0 @ X34)
% 0.46/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | ~ (v1_funct_1 @ X36)
% 0.46/0.65          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.65          | ((X39) != (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.46/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ X39 @ X38)
% 0.46/0.65              = (X37))
% 0.46/0.65          | ~ (m1_subset_1 @ X39 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.46/0.65          | ~ (v1_funct_2 @ X39 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.46/0.65          | ~ (v1_funct_1 @ X39)
% 0.46/0.65          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.46/0.65              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.46/0.65                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.46/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.46/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.46/0.65          | ~ (v1_funct_1 @ X37)
% 0.46/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | (v1_xboole_0 @ X38)
% 0.46/0.65          | (v1_xboole_0 @ X35))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X35)
% 0.46/0.65          | (v1_xboole_0 @ X38)
% 0.46/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | ~ (v1_funct_1 @ X37)
% 0.46/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.46/0.65          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.46/0.65              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.46/0.65                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.46/0.65          | ~ (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.46/0.65          | ~ (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.46/0.65               (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.46/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ 
% 0.46/0.65              (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ X38) = (
% 0.46/0.65              X37))
% 0.46/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.65          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.65          | ~ (v1_funct_1 @ X36)
% 0.46/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | (v1_xboole_0 @ X34)
% 0.46/0.65          | (v1_xboole_0 @ X33))),
% 0.46/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65            = (sk_E))
% 0.46/0.65        | ~ (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.46/0.65        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.46/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['45', '47'])).
% 0.46/0.65  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 0.46/0.65          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_r1_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.46/0.65       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X16)
% 0.46/0.65          | (v1_xboole_0 @ X17)
% 0.46/0.65          | (r1_xboole_0 @ X16 @ X17)
% 0.46/0.65          | ~ (r1_subset_1 @ X16 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.65  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.46/0.65      inference('clc', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.46/0.65      inference('clc', [status(thm)], ['60', '61'])).
% 0.46/0.65  thf(d7_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.65  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k2_partfun1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.46/0.65          | ~ (v1_funct_1 @ X29)
% 0.46/0.65          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ sk_E))),
% 0.46/0.65      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.65  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf(t4_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(cc2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.65         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('72', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.46/0.65      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.65  thf(t209_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.46/0.65          | ~ (v4_relat_1 @ X12 @ X13)
% 0.46/0.65          | ~ (v1_relat_1 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.65          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(cc1_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( v1_relat_1 @ C ) ))).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         ((v1_relat_1 @ X18)
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.65  thf('77', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['74', '77'])).
% 0.46/0.65  thf(t95_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ B ) =>
% 0.46/0.65       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         (((k7_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 0.46/0.65          | (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.46/0.65          | ~ (v1_relat_1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.65          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.65  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.65  thf(t60_relat_1, axiom,
% 0.46/0.65    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.65     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.46/0.65  thf('84', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['83'])).
% 0.46/0.65  thf('85', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc5_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.65             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.46/0.65          | (v1_partfun1 @ X24 @ X25)
% 0.46/0.65          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.46/0.65          | ~ (v1_funct_1 @ X24)
% 0.46/0.65          | (v1_xboole_0 @ X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.46/0.65        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.65  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('89', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('90', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.46/0.65      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.46/0.65  thf('91', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('92', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.46/0.65      inference('clc', [status(thm)], ['90', '91'])).
% 0.46/0.65  thf(d4_partfun1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (![X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (v1_partfun1 @ X28 @ X27)
% 0.46/0.65          | ((k1_relat_1 @ X28) = (X27))
% 0.46/0.65          | ~ (v4_relat_1 @ X28 @ X27)
% 0.46/0.65          | ~ (v1_relat_1 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_E)
% 0.46/0.65        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.46/0.65        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         ((v1_relat_1 @ X18)
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.65  thf('97', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.65  thf('98', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.65         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('100', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.46/0.65      inference('sup-', [status(thm)], ['98', '99'])).
% 0.46/0.65  thf('101', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.46/0.65      inference('demod', [status(thm)], ['94', '97', '100'])).
% 0.46/0.65  thf(t187_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.46/0.65           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.65  thf('102', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X10 @ (k1_relat_1 @ X11))
% 0.46/0.65          | ((k7_relat_1 @ X11 @ X10) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.46/0.65          | ~ (v1_relat_1 @ sk_E)
% 0.46/0.65          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.65  thf('104', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.65  thf('105', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.46/0.65          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['103', '104'])).
% 0.46/0.65  thf('106', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['84', '105'])).
% 0.46/0.65  thf('107', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('108', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('109', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('110', plain,
% 0.46/0.65      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.46/0.65          | ~ (v1_funct_1 @ X29)
% 0.46/0.65          | ((k2_partfun1 @ X30 @ X31 @ X29 @ X32) = (k7_relat_1 @ X29 @ X32)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ sk_F))),
% 0.46/0.65      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.65  thf('112', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('113', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['111', '112'])).
% 0.46/0.65  thf('114', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['83'])).
% 0.46/0.65  thf('115', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('116', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.46/0.65          | (v1_partfun1 @ X24 @ X25)
% 0.46/0.65          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.46/0.65          | ~ (v1_funct_1 @ X24)
% 0.46/0.65          | (v1_xboole_0 @ X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.65  thf('117', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.46/0.65        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.65  thf('118', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('119', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('120', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.46/0.65  thf('121', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('122', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.46/0.65      inference('clc', [status(thm)], ['120', '121'])).
% 0.46/0.65  thf('123', plain,
% 0.46/0.65      (![X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (v1_partfun1 @ X28 @ X27)
% 0.46/0.65          | ((k1_relat_1 @ X28) = (X27))
% 0.46/0.65          | ~ (v4_relat_1 @ X28 @ X27)
% 0.46/0.65          | ~ (v1_relat_1 @ X28))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.65  thf('124', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_F)
% 0.46/0.65        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.46/0.65        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['122', '123'])).
% 0.46/0.65  thf('125', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('126', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         ((v1_relat_1 @ X18)
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.65  thf('127', plain, ((v1_relat_1 @ sk_F)),
% 0.46/0.65      inference('sup-', [status(thm)], ['125', '126'])).
% 0.46/0.65  thf('128', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.65         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('130', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.46/0.65      inference('sup-', [status(thm)], ['128', '129'])).
% 0.46/0.65  thf('131', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['124', '127', '130'])).
% 0.46/0.65  thf('132', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X10 @ (k1_relat_1 @ X11))
% 0.46/0.65          | ((k7_relat_1 @ X11 @ X10) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.46/0.65  thf('133', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.46/0.65          | ~ (v1_relat_1 @ sk_F)
% 0.46/0.65          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['131', '132'])).
% 0.46/0.65  thf('134', plain, ((v1_relat_1 @ sk_F)),
% 0.46/0.65      inference('sup-', [status(thm)], ['125', '126'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.46/0.65          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['133', '134'])).
% 0.46/0.65  thf('136', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['114', '135'])).
% 0.46/0.65  thf('137', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('138', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('139', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('140', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('141', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65            = (sk_E))
% 0.46/0.65        | ~ (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)],
% 0.46/0.65                ['48', '49', '50', '51', '52', '55', '64', '69', '106', '107', 
% 0.46/0.65                 '108', '113', '136', '137', '138', '139', '140'])).
% 0.46/0.65  thf('142', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ~ (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65            = (sk_E))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['141'])).
% 0.46/0.65  thf('143', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65            = (sk_E))
% 0.46/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '142'])).
% 0.46/0.65  thf('144', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65            = (sk_E))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['143'])).
% 0.46/0.65  thf('145', plain,
% 0.46/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65            != (sk_E))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            != (sk_F)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('146', plain,
% 0.46/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65          != (sk_E)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65                = (sk_E))))),
% 0.46/0.65      inference('split', [status(esa)], ['145'])).
% 0.46/0.65  thf('147', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['83'])).
% 0.46/0.65  thf('148', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X10 @ (k1_relat_1 @ X11))
% 0.46/0.65          | ((k7_relat_1 @ X11 @ X10) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_relat_1 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.46/0.65  thf('149', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['147', '148'])).
% 0.46/0.65  thf('150', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['147', '148'])).
% 0.46/0.65  thf('151', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['111', '112'])).
% 0.46/0.65  thf('152', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('153', plain,
% 0.46/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('split', [status(esa)], ['145'])).
% 0.46/0.65  thf('154', plain,
% 0.46/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['152', '153'])).
% 0.46/0.65  thf('155', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('156', plain,
% 0.46/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.46/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['154', '155'])).
% 0.46/0.65  thf('157', plain,
% 0.46/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.46/0.65          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['151', '156'])).
% 0.46/0.65  thf('158', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('159', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('160', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('161', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.46/0.65  thf('162', plain,
% 0.46/0.65      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65         | ~ (v1_relat_1 @ sk_F)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['150', '161'])).
% 0.46/0.65  thf('163', plain, ((v1_relat_1 @ sk_F)),
% 0.46/0.65      inference('sup-', [status(thm)], ['125', '126'])).
% 0.46/0.65  thf('164', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['162', '163'])).
% 0.46/0.65  thf('165', plain,
% 0.46/0.65      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['149', '164'])).
% 0.46/0.65  thf('166', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.65  thf('167', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['165', '166'])).
% 0.46/0.65  thf('168', plain,
% 0.46/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['167'])).
% 0.46/0.65  thf('169', plain,
% 0.46/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('170', plain,
% 0.46/0.65      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('171', plain,
% 0.46/0.65      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('172', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X33)
% 0.46/0.65          | (v1_xboole_0 @ X34)
% 0.46/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | ~ (v1_funct_1 @ X36)
% 0.46/0.65          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.65          | ((X39) != (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.46/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ X39 @ X34)
% 0.46/0.65              = (X36))
% 0.46/0.65          | ~ (m1_subset_1 @ X39 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.46/0.65          | ~ (v1_funct_2 @ X39 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.46/0.65          | ~ (v1_funct_1 @ X39)
% 0.46/0.65          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.46/0.65              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.46/0.65                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.46/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.46/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.46/0.65          | ~ (v1_funct_1 @ X37)
% 0.46/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | (v1_xboole_0 @ X38)
% 0.46/0.65          | (v1_xboole_0 @ X35))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.46/0.65  thf('173', plain,
% 0.46/0.65      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X35)
% 0.46/0.65          | (v1_xboole_0 @ X38)
% 0.46/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | ~ (v1_funct_1 @ X37)
% 0.46/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X33)))
% 0.46/0.65          | ((k2_partfun1 @ X38 @ X33 @ X37 @ (k9_subset_1 @ X35 @ X38 @ X34))
% 0.46/0.65              != (k2_partfun1 @ X34 @ X33 @ X36 @ 
% 0.46/0.65                  (k9_subset_1 @ X35 @ X38 @ X34)))
% 0.46/0.65          | ~ (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36))
% 0.46/0.65          | ~ (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.46/0.65               (k4_subset_1 @ X35 @ X38 @ X34) @ X33)
% 0.46/0.65          | ~ (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33)))
% 0.46/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X35 @ X38 @ X34) @ X33 @ 
% 0.46/0.65              (k1_tmap_1 @ X35 @ X33 @ X38 @ X34 @ X37 @ X36) @ X34) = (
% 0.46/0.65              X36))
% 0.46/0.65          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.65          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.65          | ~ (v1_funct_1 @ X36)
% 0.46/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.65          | (v1_xboole_0 @ X34)
% 0.46/0.65          | (v1_xboole_0 @ X33))),
% 0.46/0.65      inference('simplify', [status(thm)], ['172'])).
% 0.46/0.65  thf('174', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | ~ (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.46/0.65            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.46/0.65        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.46/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['171', '173'])).
% 0.46/0.65  thf('175', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('176', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('177', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('178', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('179', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('180', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('181', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('182', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['84', '105'])).
% 0.46/0.65  thf('183', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('184', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('185', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['111', '112'])).
% 0.46/0.65  thf('186', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['114', '135'])).
% 0.46/0.65  thf('187', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('188', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('189', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('190', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('191', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | ~ (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)],
% 0.46/0.65                ['174', '175', '176', '177', '178', '179', '180', '181', 
% 0.46/0.65                 '182', '183', '184', '185', '186', '187', '188', '189', '190'])).
% 0.46/0.65  thf('192', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ~ (v1_funct_2 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['191'])).
% 0.46/0.65  thf('193', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['170', '192'])).
% 0.46/0.65  thf('194', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['193'])).
% 0.46/0.65  thf('195', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['169', '194'])).
% 0.46/0.65  thf('196', plain,
% 0.46/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['195'])).
% 0.46/0.65  thf('197', plain,
% 0.46/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          != (sk_F)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65                = (sk_F))))),
% 0.46/0.65      inference('split', [status(esa)], ['145'])).
% 0.46/0.65  thf('198', plain,
% 0.46/0.65      (((((sk_F) != (sk_F))
% 0.46/0.65         | (v1_xboole_0 @ sk_D)
% 0.46/0.65         | (v1_xboole_0 @ sk_C)
% 0.46/0.65         | (v1_xboole_0 @ sk_B)
% 0.46/0.65         | (v1_xboole_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65                = (sk_F))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['196', '197'])).
% 0.46/0.65  thf('199', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B)
% 0.46/0.65         | (v1_xboole_0 @ sk_C)
% 0.46/0.65         | (v1_xboole_0 @ sk_D)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65                = (sk_F))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['198'])).
% 0.46/0.65  thf('200', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('201', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65                = (sk_F))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['199', '200'])).
% 0.46/0.65  thf('202', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('203', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65                = (sk_F))))),
% 0.46/0.65      inference('clc', [status(thm)], ['201', '202'])).
% 0.46/0.65  thf('204', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('205', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65                = (sk_F))))),
% 0.46/0.65      inference('clc', [status(thm)], ['203', '204'])).
% 0.46/0.65  thf('206', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('207', plain,
% 0.46/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          = (sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['205', '206'])).
% 0.46/0.65  thf('208', plain,
% 0.46/0.65      (~
% 0.46/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65          = (sk_E))) | 
% 0.46/0.65       ~
% 0.46/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          = (sk_F))) | 
% 0.46/0.65       ~
% 0.46/0.65       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.46/0.65          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.46/0.65             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.46/0.65      inference('split', [status(esa)], ['145'])).
% 0.46/0.65  thf('209', plain,
% 0.46/0.65      (~
% 0.46/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65          = (sk_E)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['168', '207', '208'])).
% 0.46/0.65  thf('210', plain,
% 0.46/0.65      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.46/0.65         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.46/0.65         != (sk_E))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['146', '209'])).
% 0.46/0.65  thf('211', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['144', '210'])).
% 0.46/0.65  thf('212', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '211'])).
% 0.46/0.65  thf('213', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B)
% 0.46/0.65        | (v1_xboole_0 @ sk_C)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['212'])).
% 0.46/0.65  thf('214', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('215', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['213', '214'])).
% 0.46/0.65  thf('216', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('217', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.46/0.65      inference('clc', [status(thm)], ['215', '216'])).
% 0.46/0.65  thf('218', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('219', plain, ((v1_xboole_0 @ sk_B)),
% 0.46/0.65      inference('clc', [status(thm)], ['217', '218'])).
% 0.46/0.65  thf('220', plain, ($false), inference('demod', [status(thm)], ['0', '219'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
