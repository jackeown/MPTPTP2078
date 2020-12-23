%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QHLsf9prFI

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:53 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 860 expanded)
%              Number of leaves         :   40 ( 266 expanded)
%              Depth                    :   31
%              Number of atoms          : 3612 (35099 expanded)
%              Number of equality atoms :  120 (1159 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42 ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42 ) @ ( k4_subset_1 @ X41 @ X38 @ X40 ) @ X39 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X41 @ X38 @ X40 ) @ X39 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ( X36
       != ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 @ X36 @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X35 @ X30 @ X34 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) )
       != ( k2_partfun1 @ X31 @ X30 @ X33 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X30 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X30 ) ) )
      | ( ( k2_partfun1 @ X35 @ X30 @ X34 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) )
       != ( k2_partfun1 @ X31 @ X30 @ X33 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_subset_1 @ X13 @ X14 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X27 @ X28 @ X26 @ X29 )
        = ( k7_relat_1 @ X26 @ X29 ) ) ) ),
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['81','82'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('87',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['85','88','91'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['86','87'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('99',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('100',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X27 @ X28 @ X26 @ X29 )
        = ( k7_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('106',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('108',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('118',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('121',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['115','118','121'])).

thf('123',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k7_relat_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['116','117'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','97','98','99','104','127','128','129','130','131'])).

thf('133',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
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
    inference('sup-',[status(thm)],['30','133'])).

thf('135',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('140',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['136'])).

thf('141',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('143',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('147',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','96'])).

thf('148',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('149',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','126'])).

thf('150',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148','149'])).

thf('151',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('153',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('154',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('155',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ( X36
       != ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 @ X36 @ X31 )
        = X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X35 @ X30 @ X34 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) )
       != ( k2_partfun1 @ X31 @ X30 @ X33 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('156',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X30 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X30 ) ) )
      | ( ( k2_partfun1 @ X35 @ X30 @ X34 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) )
       != ( k2_partfun1 @ X31 @ X30 @ X33 @ ( k9_subset_1 @ X32 @ X35 @ X31 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X32 @ X35 @ X31 ) @ X30 @ ( k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33 ) @ X31 )
        = X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
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
    inference('sup-',[status(thm)],['154','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('163',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('165',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','96'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('167',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('169',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','126'])).

thf('170',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
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
    inference(demod,[status(thm)],['157','158','159','160','161','162','163','164','165','166','167','168','169','170','171','172','173'])).

thf('175',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
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
    inference('sup-',[status(thm)],['153','175'])).

thf('177',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
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
    inference('sup-',[status(thm)],['152','177'])).

thf('179',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['136'])).

thf('181',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['136'])).

thf('192',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['151','190','191'])).

thf('193',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['137','192'])).

thf('194',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['135','193'])).

thf('195',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','194'])).

thf('196',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['0','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QHLsf9prFI
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 196 iterations in 0.186s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.64  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(t6_tmap_1, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.64               ( ![D:$i]:
% 0.45/0.64                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.64                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.64                   ( ( r1_subset_1 @ C @ D ) =>
% 0.45/0.64                     ( ![E:$i]:
% 0.45/0.64                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.64                           ( m1_subset_1 @
% 0.45/0.64                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.45/0.64                         ( ![F:$i]:
% 0.45/0.64                           ( ( ( v1_funct_1 @ F ) & 
% 0.45/0.64                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.64                               ( m1_subset_1 @
% 0.45/0.64                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.64                             ( ( ( k2_partfun1 @
% 0.45/0.64                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.45/0.64                                 ( k2_partfun1 @
% 0.45/0.64                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.45/0.64                               ( ( k2_partfun1 @
% 0.45/0.64                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.64                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.45/0.64                                 ( E ) ) & 
% 0.45/0.64                               ( ( k2_partfun1 @
% 0.45/0.64                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.64                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.45/0.64                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.64                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.64                  ( ![D:$i]:
% 0.45/0.64                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.64                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.64                      ( ( r1_subset_1 @ C @ D ) =>
% 0.45/0.64                        ( ![E:$i]:
% 0.45/0.64                          ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.64                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.64                              ( m1_subset_1 @
% 0.45/0.64                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.45/0.64                            ( ![F:$i]:
% 0.45/0.64                              ( ( ( v1_funct_1 @ F ) & 
% 0.45/0.64                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.64                                  ( m1_subset_1 @
% 0.45/0.64                                    F @ 
% 0.45/0.64                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.64                                ( ( ( k2_partfun1 @
% 0.45/0.64                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.45/0.64                                    ( k2_partfun1 @
% 0.45/0.64                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.45/0.64                                  ( ( k2_partfun1 @
% 0.45/0.64                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.64                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.45/0.64                                    ( E ) ) & 
% 0.45/0.64                                  ( ( k2_partfun1 @
% 0.45/0.64                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.45/0.64                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.45/0.64                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.45/0.64  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_k1_tmap_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.64         ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.64         ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.45/0.64         ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.45/0.64         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.64       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.45/0.64         ( v1_funct_2 @
% 0.45/0.64           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.64           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.45/0.64         ( m1_subset_1 @
% 0.45/0.64           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.64          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.45/0.64          | ~ (v1_funct_1 @ X37)
% 0.45/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.45/0.64          | (v1_xboole_0 @ X40)
% 0.45/0.64          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.45/0.64          | (v1_xboole_0 @ X38)
% 0.45/0.64          | (v1_xboole_0 @ X39)
% 0.45/0.64          | (v1_xboole_0 @ X41)
% 0.45/0.64          | ~ (v1_funct_1 @ X42)
% 0.45/0.64          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.45/0.64          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.45/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42)))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ X2)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.45/0.64          | (v1_xboole_0 @ X1)
% 0.45/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.45/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ X2)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.45/0.64          | (v1_xboole_0 @ X1)
% 0.45/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '8'])).
% 0.45/0.64  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.64      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '12'])).
% 0.45/0.64  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.64          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.45/0.64          | ~ (v1_funct_1 @ X37)
% 0.45/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.45/0.64          | (v1_xboole_0 @ X40)
% 0.45/0.64          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.45/0.64          | (v1_xboole_0 @ X38)
% 0.45/0.64          | (v1_xboole_0 @ X39)
% 0.45/0.64          | (v1_xboole_0 @ X41)
% 0.45/0.64          | ~ (v1_funct_1 @ X42)
% 0.45/0.64          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.45/0.64          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.45/0.64          | (v1_funct_2 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42) @ 
% 0.45/0.64             (k4_subset_1 @ X41 @ X38 @ X40) @ X39))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.64           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | (v1_xboole_0 @ X1)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.64  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.64           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | (v1_xboole_0 @ X1)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.64          | (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['17', '23'])).
% 0.45/0.64  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '27'])).
% 0.45/0.64  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.64          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.45/0.64          | ~ (v1_funct_1 @ X37)
% 0.45/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.45/0.64          | (v1_xboole_0 @ X40)
% 0.45/0.64          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.45/0.64          | (v1_xboole_0 @ X38)
% 0.45/0.64          | (v1_xboole_0 @ X39)
% 0.45/0.64          | (v1_xboole_0 @ X41)
% 0.45/0.64          | ~ (v1_funct_1 @ X42)
% 0.45/0.64          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.45/0.64          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.45/0.64          | (m1_subset_1 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42) @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X38 @ X40) @ X39))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | (v1_xboole_0 @ X1)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.45/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.45/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.45/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | (v1_xboole_0 @ X1)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.64          | (m1_subset_1 @ 
% 0.45/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '38'])).
% 0.45/0.64  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_D)
% 0.45/0.64          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.45/0.64          | (v1_xboole_0 @ sk_C)
% 0.45/0.64          | (v1_xboole_0 @ sk_B)
% 0.45/0.64          | (v1_xboole_0 @ X0)
% 0.45/0.64          | (m1_subset_1 @ 
% 0.45/0.64             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['31', '42'])).
% 0.45/0.64  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf(d1_tmap_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.45/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.64               ( ![D:$i]:
% 0.45/0.64                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.64                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.64                   ( ![E:$i]:
% 0.45/0.64                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.45/0.64                         ( m1_subset_1 @
% 0.45/0.64                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.45/0.64                       ( ![F:$i]:
% 0.45/0.64                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.45/0.64                             ( m1_subset_1 @
% 0.45/0.64                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.45/0.64                           ( ( ( k2_partfun1 @
% 0.45/0.64                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.45/0.64                               ( k2_partfun1 @
% 0.45/0.64                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.45/0.64                             ( ![G:$i]:
% 0.45/0.64                               ( ( ( v1_funct_1 @ G ) & 
% 0.45/0.64                                   ( v1_funct_2 @
% 0.45/0.64                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.45/0.64                                   ( m1_subset_1 @
% 0.45/0.64                                     G @ 
% 0.45/0.64                                     ( k1_zfmisc_1 @
% 0.45/0.64                                       ( k2_zfmisc_1 @
% 0.45/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.45/0.64                                 ( ( ( G ) =
% 0.45/0.64                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.45/0.64                                   ( ( ( k2_partfun1 @
% 0.45/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.45/0.64                                         C ) =
% 0.45/0.64                                       ( E ) ) & 
% 0.45/0.64                                     ( ( k2_partfun1 @
% 0.45/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.45/0.64                                         D ) =
% 0.45/0.64                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ X30)
% 0.45/0.64          | (v1_xboole_0 @ X31)
% 0.45/0.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | ~ (v1_funct_1 @ X33)
% 0.45/0.64          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.64          | ((X36) != (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.45/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ X36 @ X35)
% 0.45/0.64              = (X34))
% 0.45/0.64          | ~ (m1_subset_1 @ X36 @ 
% 0.45/0.64               (k1_zfmisc_1 @ 
% 0.45/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.45/0.64          | ~ (v1_funct_2 @ X36 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X36)
% 0.45/0.64          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.45/0.64              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.45/0.64                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.45/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.45/0.64          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X34)
% 0.45/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | (v1_xboole_0 @ X35)
% 0.45/0.64          | (v1_xboole_0 @ X32))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ X32)
% 0.45/0.64          | (v1_xboole_0 @ X35)
% 0.45/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | ~ (v1_funct_1 @ X34)
% 0.45/0.64          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.45/0.64          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.45/0.64              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.45/0.64                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.45/0.64          | ~ (v1_funct_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.45/0.64          | ~ (v1_funct_2 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.45/0.64               (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.45/0.64               (k1_zfmisc_1 @ 
% 0.45/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.45/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ 
% 0.45/0.64              (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ X35) = (
% 0.45/0.64              X34))
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.64          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X33)
% 0.45/0.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | (v1_xboole_0 @ X31)
% 0.45/0.64          | (v1_xboole_0 @ X30))),
% 0.45/0.64      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64            = (sk_E))
% 0.45/0.64        | ~ (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.45/0.64        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.45/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '47'])).
% 0.45/0.64  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k9_subset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.64       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.64         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.45/0.64          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_r1_subset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.45/0.64       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ X13)
% 0.45/0.64          | (v1_xboole_0 @ X14)
% 0.45/0.64          | (r1_xboole_0 @ X13 @ X14)
% 0.45/0.64          | ~ (r1_subset_1 @ X13 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.64  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.64      inference('clc', [status(thm)], ['58', '59'])).
% 0.45/0.64  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.45/0.64      inference('clc', [status(thm)], ['60', '61'])).
% 0.45/0.64  thf(d7_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k2_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.45/0.64          | ~ (v1_funct_1 @ X26)
% 0.45/0.64          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ sk_E))),
% 0.45/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.64  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf(t2_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('71', plain,
% 0.45/0.64      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.64  thf('72', plain,
% 0.45/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['70', '71'])).
% 0.45/0.64  thf('73', plain,
% 0.45/0.64      (![X2 : $i, X4 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.64  thf('75', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.64      inference('simplify', [status(thm)], ['74'])).
% 0.45/0.64  thf('76', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc5_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('77', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.64          | (v1_partfun1 @ X21 @ X22)
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.45/0.64          | ~ (v1_funct_1 @ X21)
% 0.45/0.64          | (v1_xboole_0 @ X23))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('78', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.45/0.64        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.64  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('80', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('81', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.45/0.64  thf('82', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('83', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.45/0.64      inference('clc', [status(thm)], ['81', '82'])).
% 0.45/0.64  thf(d4_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.64  thf('84', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X25 @ X24)
% 0.45/0.64          | ((k1_relat_1 @ X25) = (X24))
% 0.45/0.64          | ~ (v4_relat_1 @ X25 @ X24)
% 0.45/0.64          | ~ (v1_relat_1 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('85', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_E)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.45/0.64        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('87', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X15)
% 0.45/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.64      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.64  thf('89', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('90', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X18 @ X19)
% 0.45/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('91', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.45/0.64  thf('92', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['85', '88', '91'])).
% 0.45/0.64  thf(t187_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.45/0.64           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.45/0.64  thf('93', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 0.45/0.64          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ X12))),
% 0.45/0.64      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.45/0.64  thf('94', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.45/0.64          | ~ (v1_relat_1 @ sk_E)
% 0.45/0.64          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.64  thf('95', plain, ((v1_relat_1 @ sk_E)),
% 0.45/0.64      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.45/0.64          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.64  thf('97', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['75', '96'])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('99', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('100', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('101', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.45/0.64          | ~ (v1_funct_1 @ X26)
% 0.45/0.64          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.45/0.64  thf('102', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ sk_F))),
% 0.45/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.45/0.64  thf('103', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.64  thf('105', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.64      inference('simplify', [status(thm)], ['74'])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('107', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.64          | (v1_partfun1 @ X21 @ X22)
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.45/0.64          | ~ (v1_funct_1 @ X21)
% 0.45/0.64          | (v1_xboole_0 @ X23))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.64        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('109', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('110', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('111', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.45/0.64  thf('112', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('113', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.45/0.64      inference('clc', [status(thm)], ['111', '112'])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      (![X24 : $i, X25 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X25 @ X24)
% 0.45/0.64          | ((k1_relat_1 @ X25) = (X24))
% 0.45/0.64          | ~ (v4_relat_1 @ X25 @ X24)
% 0.45/0.64          | ~ (v1_relat_1 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('115', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_F)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.45/0.64        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['113', '114'])).
% 0.45/0.64  thf('116', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('117', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X15)
% 0.45/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('118', plain, ((v1_relat_1 @ sk_F)),
% 0.45/0.64      inference('sup-', [status(thm)], ['116', '117'])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X18 @ X19)
% 0.45/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('121', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.45/0.64      inference('sup-', [status(thm)], ['119', '120'])).
% 0.45/0.64  thf('122', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['115', '118', '121'])).
% 0.45/0.64  thf('123', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 0.45/0.64          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ X12))),
% 0.45/0.64      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.45/0.64          | ~ (v1_relat_1 @ sk_F)
% 0.45/0.64          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['122', '123'])).
% 0.45/0.64  thf('125', plain, ((v1_relat_1 @ sk_F)),
% 0.45/0.64      inference('sup-', [status(thm)], ['116', '117'])).
% 0.45/0.64  thf('126', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.45/0.64          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.64  thf('127', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['105', '126'])).
% 0.45/0.64  thf('128', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('129', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('131', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('132', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64            = (sk_E))
% 0.45/0.64        | ~ (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['48', '49', '50', '51', '52', '55', '64', '69', '97', '98', 
% 0.45/0.64                 '99', '104', '127', '128', '129', '130', '131'])).
% 0.45/0.64  thf('133', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ~ (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64            = (sk_E))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify', [status(thm)], ['132'])).
% 0.45/0.64  thf('134', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64            = (sk_E))
% 0.45/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['30', '133'])).
% 0.45/0.64  thf('135', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64            = (sk_E))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify', [status(thm)], ['134'])).
% 0.45/0.64  thf('136', plain,
% 0.45/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64            != (sk_E))
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            != (sk_F)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('137', plain,
% 0.45/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64          != (sk_E)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64                = (sk_E))))),
% 0.45/0.64      inference('split', [status(esa)], ['136'])).
% 0.45/0.64  thf('138', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.64  thf('139', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('140', plain,
% 0.45/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.64      inference('split', [status(esa)], ['136'])).
% 0.45/0.64  thf('141', plain,
% 0.45/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['139', '140'])).
% 0.45/0.64  thf('142', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('143', plain,
% 0.45/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.45/0.64          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['141', '142'])).
% 0.45/0.64  thf('144', plain,
% 0.45/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.45/0.64          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['138', '143'])).
% 0.45/0.64  thf('145', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('146', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('147', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['75', '96'])).
% 0.45/0.64  thf('148', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('149', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['105', '126'])).
% 0.45/0.64  thf('150', plain,
% 0.45/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['144', '145', '146', '147', '148', '149'])).
% 0.45/0.64  thf('151', plain,
% 0.45/0.64      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['150'])).
% 0.45/0.64  thf('152', plain,
% 0.45/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf('153', plain,
% 0.45/0.64      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('154', plain,
% 0.45/0.64      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.64  thf('155', plain,
% 0.45/0.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ X30)
% 0.45/0.64          | (v1_xboole_0 @ X31)
% 0.45/0.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | ~ (v1_funct_1 @ X33)
% 0.45/0.64          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.64          | ((X36) != (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.45/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ X36 @ X31)
% 0.45/0.64              = (X33))
% 0.45/0.64          | ~ (m1_subset_1 @ X36 @ 
% 0.45/0.64               (k1_zfmisc_1 @ 
% 0.45/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.45/0.64          | ~ (v1_funct_2 @ X36 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X36)
% 0.45/0.64          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.45/0.64              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.45/0.64                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.45/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.45/0.64          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X34)
% 0.45/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | (v1_xboole_0 @ X35)
% 0.45/0.64          | (v1_xboole_0 @ X32))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.45/0.64  thf('156', plain,
% 0.45/0.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ X32)
% 0.45/0.64          | (v1_xboole_0 @ X35)
% 0.45/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | ~ (v1_funct_1 @ X34)
% 0.45/0.64          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.45/0.64          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.45/0.64              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.45/0.64                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.45/0.64          | ~ (v1_funct_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.45/0.64          | ~ (v1_funct_2 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.45/0.64               (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.45/0.64               (k1_zfmisc_1 @ 
% 0.45/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.45/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ 
% 0.45/0.64              (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ X31) = (
% 0.45/0.64              X33))
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.64          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.45/0.64          | ~ (v1_funct_1 @ X33)
% 0.45/0.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.45/0.64          | (v1_xboole_0 @ X31)
% 0.45/0.64          | (v1_xboole_0 @ X30))),
% 0.45/0.64      inference('simplify', [status(thm)], ['155'])).
% 0.45/0.64  thf('157', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            = (sk_F))
% 0.45/0.64        | ~ (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.45/0.64            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.45/0.64        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.45/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['154', '156'])).
% 0.45/0.64  thf('158', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('159', plain, ((v1_funct_1 @ sk_F)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('160', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('161', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('162', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('163', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('164', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('165', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['75', '96'])).
% 0.45/0.64  thf('166', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.45/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.64  thf('167', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.64  thf('168', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.64  thf('169', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['105', '126'])).
% 0.45/0.64  thf('170', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('171', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('172', plain, ((v1_funct_1 @ sk_E)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('173', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('174', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            = (sk_F))
% 0.45/0.64        | ~ (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)],
% 0.45/0.64                ['157', '158', '159', '160', '161', '162', '163', '164', 
% 0.45/0.64                 '165', '166', '167', '168', '169', '170', '171', '172', '173'])).
% 0.45/0.64  thf('175', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ~ (v1_funct_2 @ 
% 0.45/0.64             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.45/0.64             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            = (sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify', [status(thm)], ['174'])).
% 0.45/0.64  thf('176', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            = (sk_F))
% 0.45/0.64        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['153', '175'])).
% 0.45/0.64  thf('177', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            = (sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify', [status(thm)], ['176'])).
% 0.45/0.64  thf('178', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64            = (sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['152', '177'])).
% 0.45/0.64  thf('179', plain,
% 0.45/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64          = (sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify', [status(thm)], ['178'])).
% 0.45/0.64  thf('180', plain,
% 0.45/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64          != (sk_F)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64                = (sk_F))))),
% 0.45/0.64      inference('split', [status(esa)], ['136'])).
% 0.45/0.64  thf('181', plain,
% 0.45/0.64      (((((sk_F) != (sk_F))
% 0.45/0.64         | (v1_xboole_0 @ sk_D)
% 0.45/0.64         | (v1_xboole_0 @ sk_C)
% 0.45/0.64         | (v1_xboole_0 @ sk_B)
% 0.45/0.64         | (v1_xboole_0 @ sk_A)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64                = (sk_F))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['179', '180'])).
% 0.45/0.64  thf('182', plain,
% 0.45/0.64      ((((v1_xboole_0 @ sk_A)
% 0.45/0.64         | (v1_xboole_0 @ sk_B)
% 0.45/0.64         | (v1_xboole_0 @ sk_C)
% 0.45/0.64         | (v1_xboole_0 @ sk_D)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64                = (sk_F))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['181'])).
% 0.45/0.64  thf('183', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('184', plain,
% 0.45/0.64      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64                = (sk_F))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['182', '183'])).
% 0.45/0.64  thf('185', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('186', plain,
% 0.45/0.64      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64                = (sk_F))))),
% 0.45/0.64      inference('clc', [status(thm)], ['184', '185'])).
% 0.45/0.64  thf('187', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('188', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_B))
% 0.45/0.64         <= (~
% 0.45/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64                = (sk_F))))),
% 0.45/0.64      inference('clc', [status(thm)], ['186', '187'])).
% 0.45/0.64  thf('189', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('190', plain,
% 0.45/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64          = (sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['188', '189'])).
% 0.45/0.64  thf('191', plain,
% 0.45/0.64      (~
% 0.45/0.64       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64          = (sk_E))) | 
% 0.45/0.64       ~
% 0.45/0.64       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.45/0.64          = (sk_F))) | 
% 0.45/0.64       ~
% 0.45/0.64       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.45/0.64          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.45/0.64             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.45/0.64      inference('split', [status(esa)], ['136'])).
% 0.45/0.64  thf('192', plain,
% 0.45/0.64      (~
% 0.45/0.64       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64          = (sk_E)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['151', '190', '191'])).
% 0.45/0.64  thf('193', plain,
% 0.45/0.64      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.45/0.64         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.45/0.64         != (sk_E))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['137', '192'])).
% 0.45/0.64  thf('194', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['135', '193'])).
% 0.45/0.64  thf('195', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_D)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '194'])).
% 0.45/0.64  thf('196', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_A)
% 0.45/0.64        | (v1_xboole_0 @ sk_B)
% 0.45/0.64        | (v1_xboole_0 @ sk_C)
% 0.45/0.64        | (v1_xboole_0 @ sk_D))),
% 0.45/0.64      inference('simplify', [status(thm)], ['195'])).
% 0.45/0.64  thf('197', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('198', plain,
% 0.45/0.64      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['196', '197'])).
% 0.45/0.64  thf('199', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('200', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.45/0.64      inference('clc', [status(thm)], ['198', '199'])).
% 0.45/0.64  thf('201', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('202', plain, ((v1_xboole_0 @ sk_B)),
% 0.45/0.64      inference('clc', [status(thm)], ['200', '201'])).
% 0.45/0.64  thf('203', plain, ($false), inference('demod', [status(thm)], ['0', '202'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
