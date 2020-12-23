%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RY0w90nXCs

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:55 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 861 expanded)
%              Number of leaves         :   40 ( 266 expanded)
%              Depth                    :   30
%              Number of atoms          : 3643 (35110 expanded)
%              Number of equality atoms :  120 (1144 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

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
    inference('sup-',[status(thm)],['73','74'])).

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
    inference('sup-',[status(thm)],['15','135'])).

thf('137',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('142',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['138'])).

thf('143',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('149',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','96'])).

thf('150',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('151',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','126'])).

thf('152',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151'])).

thf('153',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('155',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('156',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('157',plain,(
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

thf('158',plain,(
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
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
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
    inference('sup-',[status(thm)],['156','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('165',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('167',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','96'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('169',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('171',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['105','126'])).

thf('172',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
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
    inference(demod,[status(thm)],['159','160','161','162','163','164','165','166','167','168','169','170','171','172','173','174','175'])).

thf('177',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
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
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['155','177'])).

thf('179',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
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
    inference('sup-',[status(thm)],['154','179'])).

thf('181',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['138'])).

thf('183',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['138'])).

thf('194',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['153','192','193'])).

thf('195',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['139','194'])).

thf('196',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    $false ),
    inference(demod,[status(thm)],['0','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RY0w90nXCs
% 0.11/0.34  % Computer   : n021.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 20:44:05 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.35  % Python version: Python 3.6.8
% 0.11/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 185 iterations in 0.156s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.61  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.61  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
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
% 0.44/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.61          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.44/0.61          | ~ (v1_funct_1 @ X37)
% 0.44/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.44/0.61          | (v1_xboole_0 @ X40)
% 0.44/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.44/0.61          | (v1_xboole_0 @ X38)
% 0.44/0.61          | (v1_xboole_0 @ X39)
% 0.44/0.61          | (v1_xboole_0 @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X42)
% 0.44/0.61          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.44/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.44/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42)))),
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
% 0.44/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.61          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.44/0.61          | ~ (v1_funct_1 @ X37)
% 0.44/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.44/0.61          | (v1_xboole_0 @ X40)
% 0.44/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.44/0.61          | (v1_xboole_0 @ X38)
% 0.44/0.61          | (v1_xboole_0 @ X39)
% 0.44/0.61          | (v1_xboole_0 @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X42)
% 0.44/0.61          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.44/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.44/0.61          | (v1_funct_2 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42) @ 
% 0.44/0.61             (k4_subset_1 @ X41 @ X38 @ X40) @ X39))),
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
% 0.44/0.61      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.61          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.44/0.61          | ~ (v1_funct_1 @ X37)
% 0.44/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.44/0.61          | (v1_xboole_0 @ X40)
% 0.44/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.44/0.61          | (v1_xboole_0 @ X38)
% 0.44/0.61          | (v1_xboole_0 @ X39)
% 0.44/0.61          | (v1_xboole_0 @ X41)
% 0.44/0.61          | ~ (v1_funct_1 @ X42)
% 0.44/0.61          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.44/0.61          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.44/0.61          | (m1_subset_1 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42) @ 
% 0.44/0.61             (k1_zfmisc_1 @ 
% 0.44/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X38 @ X40) @ X39))))),
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
% 0.44/0.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X30)
% 0.44/0.61          | (v1_xboole_0 @ X31)
% 0.44/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | ~ (v1_funct_1 @ X33)
% 0.44/0.61          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.61          | ((X36) != (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ X36 @ X35)
% 0.44/0.61              = (X34))
% 0.44/0.61          | ~ (m1_subset_1 @ X36 @ 
% 0.44/0.61               (k1_zfmisc_1 @ 
% 0.44/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.61          | ~ (v1_funct_2 @ X36 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.61          | ~ (v1_funct_1 @ X36)
% 0.44/0.61          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.61              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.61                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.61          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.61          | ~ (v1_funct_1 @ X34)
% 0.44/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | (v1_xboole_0 @ X35)
% 0.44/0.61          | (v1_xboole_0 @ X32))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.61  thf('47', plain,
% 0.44/0.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X32)
% 0.44/0.61          | (v1_xboole_0 @ X35)
% 0.44/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | ~ (v1_funct_1 @ X34)
% 0.44/0.61          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.61          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.61              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.61                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.61               (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.61               (k1_zfmisc_1 @ 
% 0.44/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ 
% 0.44/0.61              (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ X35) = (
% 0.44/0.61              X34))
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.61          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.61          | ~ (v1_funct_1 @ X33)
% 0.44/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | (v1_xboole_0 @ X31)
% 0.44/0.61          | (v1_xboole_0 @ X30))),
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
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.61       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.61  thf('57', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X13)
% 0.44/0.61          | (v1_xboole_0 @ X14)
% 0.44/0.61          | (r1_xboole_0 @ X13 @ X14)
% 0.44/0.61          | ~ (r1_subset_1 @ X13 @ X14))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.61  thf('58', plain,
% 0.44/0.61      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.61  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.44/0.61  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.44/0.61      inference('clc', [status(thm)], ['60', '61'])).
% 0.44/0.61  thf(d7_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.61  thf('63', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.61  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('65', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.61  thf('66', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.44/0.61          | ~ (v1_funct_1 @ X26)
% 0.44/0.61          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.61  thf('67', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.61      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.61  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('69', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf(t2_boole, axiom,
% 0.44/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.61  thf('70', plain,
% 0.44/0.61      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.61  thf('71', plain,
% 0.44/0.61      (![X0 : $i, X2 : $i]:
% 0.44/0.61         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.61  thf('72', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.61  thf('73', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.44/0.61      inference('simplify', [status(thm)], ['72'])).
% 0.44/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.44/0.61  thf('74', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.44/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.44/0.61  thf('75', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.61  thf('76', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc5_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.61       ( ![C:$i]:
% 0.44/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.61  thf('77', plain,
% 0.44/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.44/0.61          | (v1_partfun1 @ X21 @ X22)
% 0.44/0.61          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.44/0.61          | ~ (v1_funct_1 @ X21)
% 0.44/0.61          | (v1_xboole_0 @ X23))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.61  thf('78', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.61        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.44/0.61  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('80', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('81', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.44/0.61  thf('82', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('83', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.44/0.61      inference('clc', [status(thm)], ['81', '82'])).
% 0.44/0.61  thf(d4_partfun1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.61       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.61  thf('84', plain,
% 0.44/0.61      (![X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (v1_partfun1 @ X25 @ X24)
% 0.44/0.61          | ((k1_relat_1 @ X25) = (X24))
% 0.44/0.61          | ~ (v4_relat_1 @ X25 @ X24)
% 0.44/0.61          | ~ (v1_relat_1 @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.61  thf('85', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ sk_E)
% 0.44/0.61        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.44/0.61        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.44/0.61  thf('86', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( v1_relat_1 @ C ) ))).
% 0.44/0.61  thf('87', plain,
% 0.44/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.61         ((v1_relat_1 @ X15)
% 0.44/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.61  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.61      inference('sup-', [status(thm)], ['86', '87'])).
% 0.44/0.61  thf('89', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc2_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.61  thf('90', plain,
% 0.44/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.61         ((v4_relat_1 @ X18 @ X19)
% 0.44/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.61  thf('91', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.44/0.61      inference('sup-', [status(thm)], ['89', '90'])).
% 0.44/0.61  thf('92', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['85', '88', '91'])).
% 0.44/0.61  thf(t187_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.61           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.61  thf('93', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.61          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.61  thf('94', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_E)
% 0.44/0.61          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['92', '93'])).
% 0.44/0.61  thf('95', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.61      inference('sup-', [status(thm)], ['86', '87'])).
% 0.44/0.61  thf('96', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.61          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['94', '95'])).
% 0.44/0.61  thf('97', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['75', '96'])).
% 0.44/0.61  thf('98', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('99', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('100', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('101', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.44/0.61          | ~ (v1_funct_1 @ X26)
% 0.44/0.61          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.61  thf('102', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.61          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.61      inference('sup-', [status(thm)], ['100', '101'])).
% 0.44/0.61  thf('103', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('104', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.44/0.61  thf('105', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.61  thf('106', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('107', plain,
% 0.44/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.44/0.61          | (v1_partfun1 @ X21 @ X22)
% 0.44/0.61          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.44/0.61          | ~ (v1_funct_1 @ X21)
% 0.44/0.61          | (v1_xboole_0 @ X23))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.61  thf('108', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.61        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['106', '107'])).
% 0.44/0.61  thf('109', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('110', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('111', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.44/0.61  thf('112', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('113', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.44/0.61      inference('clc', [status(thm)], ['111', '112'])).
% 0.44/0.61  thf('114', plain,
% 0.44/0.61      (![X24 : $i, X25 : $i]:
% 0.44/0.61         (~ (v1_partfun1 @ X25 @ X24)
% 0.44/0.61          | ((k1_relat_1 @ X25) = (X24))
% 0.44/0.61          | ~ (v4_relat_1 @ X25 @ X24)
% 0.44/0.61          | ~ (v1_relat_1 @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.61  thf('115', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ sk_F)
% 0.44/0.61        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.44/0.61        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['113', '114'])).
% 0.44/0.61  thf('116', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('117', plain,
% 0.44/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.61         ((v1_relat_1 @ X15)
% 0.44/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.61  thf('118', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.61      inference('sup-', [status(thm)], ['116', '117'])).
% 0.44/0.61  thf('119', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('120', plain,
% 0.44/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.61         ((v4_relat_1 @ X18 @ X19)
% 0.44/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.61  thf('121', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.44/0.61      inference('sup-', [status(thm)], ['119', '120'])).
% 0.44/0.61  thf('122', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['115', '118', '121'])).
% 0.44/0.61  thf('123', plain,
% 0.44/0.61      (![X11 : $i, X12 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.61          | ((k7_relat_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X12))),
% 0.44/0.61      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.61  thf('124', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_F)
% 0.44/0.61          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['122', '123'])).
% 0.44/0.61  thf('125', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.61      inference('sup-', [status(thm)], ['116', '117'])).
% 0.44/0.61  thf('126', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.61          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['124', '125'])).
% 0.44/0.61  thf('127', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['105', '126'])).
% 0.44/0.61  thf('128', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('129', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('131', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('132', plain,
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
% 0.44/0.61                ['48', '49', '50', '51', '52', '55', '64', '69', '97', '98', 
% 0.44/0.61                 '99', '104', '127', '128', '129', '130', '131'])).
% 0.44/0.61  thf('133', plain,
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
% 0.44/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.44/0.61  thf('134', plain,
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
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '133'])).
% 0.44/0.61  thf('135', plain,
% 0.44/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61            = (sk_E))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['134'])).
% 0.44/0.61  thf('136', plain,
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
% 0.44/0.61            = (sk_E)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['15', '135'])).
% 0.44/0.61  thf('137', plain,
% 0.44/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61          = (sk_E))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['136'])).
% 0.44/0.61  thf('138', plain,
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
% 0.44/0.61  thf('139', plain,
% 0.44/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61          != (sk_E)))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.61                = (sk_E))))),
% 0.44/0.61      inference('split', [status(esa)], ['138'])).
% 0.44/0.61  thf('140', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.44/0.61  thf('141', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('142', plain,
% 0.44/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.61      inference('split', [status(esa)], ['138'])).
% 0.44/0.61  thf('143', plain,
% 0.44/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['141', '142'])).
% 0.44/0.61  thf('144', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('145', plain,
% 0.44/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.44/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.61      inference('demod', [status(thm)], ['143', '144'])).
% 0.44/0.61  thf('146', plain,
% 0.44/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.44/0.61          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['140', '145'])).
% 0.44/0.61  thf('147', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('148', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf('149', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['75', '96'])).
% 0.44/0.61  thf('150', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('151', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['105', '126'])).
% 0.44/0.61  thf('152', plain,
% 0.44/0.61      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.61      inference('demod', [status(thm)],
% 0.44/0.61                ['146', '147', '148', '149', '150', '151'])).
% 0.44/0.61  thf('153', plain,
% 0.44/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.61          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.61             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.61      inference('simplify', [status(thm)], ['152'])).
% 0.44/0.61  thf('154', plain,
% 0.44/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('155', plain,
% 0.44/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.61  thf('156', plain,
% 0.44/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61         (k1_zfmisc_1 @ 
% 0.44/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.61  thf('157', plain,
% 0.44/0.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X30)
% 0.44/0.61          | (v1_xboole_0 @ X31)
% 0.44/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | ~ (v1_funct_1 @ X33)
% 0.44/0.61          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.61          | ((X36) != (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ X36 @ X31)
% 0.44/0.61              = (X33))
% 0.44/0.61          | ~ (m1_subset_1 @ X36 @ 
% 0.44/0.61               (k1_zfmisc_1 @ 
% 0.44/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.61          | ~ (v1_funct_2 @ X36 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.61          | ~ (v1_funct_1 @ X36)
% 0.44/0.61          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.61              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.61                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.61          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.61          | ~ (v1_funct_1 @ X34)
% 0.44/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | (v1_xboole_0 @ X35)
% 0.44/0.61          | (v1_xboole_0 @ X32))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.61  thf('158', plain,
% 0.44/0.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.61         ((v1_xboole_0 @ X32)
% 0.44/0.61          | (v1_xboole_0 @ X35)
% 0.44/0.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | ~ (v1_funct_1 @ X34)
% 0.44/0.61          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.61          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.61              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.61                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.61               (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.61               (k1_zfmisc_1 @ 
% 0.44/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ 
% 0.44/0.61              (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ X31) = (
% 0.44/0.61              X33))
% 0.44/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.61          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.61          | ~ (v1_funct_1 @ X33)
% 0.44/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.61          | (v1_xboole_0 @ X31)
% 0.44/0.61          | (v1_xboole_0 @ X30))),
% 0.44/0.61      inference('simplify', [status(thm)], ['157'])).
% 0.44/0.61  thf('159', plain,
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
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            = (sk_F))
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
% 0.44/0.61      inference('sup-', [status(thm)], ['156', '158'])).
% 0.44/0.61  thf('160', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('161', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('162', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('163', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('164', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('165', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('166', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf('167', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['75', '96'])).
% 0.44/0.61  thf('168', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.61  thf('169', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.61  thf('170', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.44/0.61  thf('171', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['105', '126'])).
% 0.44/0.61  thf('172', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('173', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('174', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('175', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('176', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            = (sk_F))
% 0.44/0.61        | ~ (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)],
% 0.44/0.61                ['159', '160', '161', '162', '163', '164', '165', '166', 
% 0.44/0.61                 '167', '168', '169', '170', '171', '172', '173', '174', '175'])).
% 0.44/0.61  thf('177', plain,
% 0.44/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ~ (v1_funct_2 @ 
% 0.44/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            = (sk_F))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['176'])).
% 0.44/0.61  thf('178', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            = (sk_F))
% 0.44/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['155', '177'])).
% 0.44/0.61  thf('179', plain,
% 0.44/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            = (sk_F))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['178'])).
% 0.44/0.61  thf('180', plain,
% 0.44/0.61      (((v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_D)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61            = (sk_F)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['154', '179'])).
% 0.44/0.61  thf('181', plain,
% 0.44/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61          = (sk_F))
% 0.44/0.61        | (v1_xboole_0 @ sk_A)
% 0.44/0.61        | (v1_xboole_0 @ sk_B)
% 0.44/0.61        | (v1_xboole_0 @ sk_C)
% 0.44/0.61        | (v1_xboole_0 @ sk_D))),
% 0.44/0.61      inference('simplify', [status(thm)], ['180'])).
% 0.44/0.61  thf('182', plain,
% 0.44/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61          != (sk_F)))
% 0.44/0.61         <= (~
% 0.44/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.61                = (sk_F))))),
% 0.44/0.61      inference('split', [status(esa)], ['138'])).
% 0.44/0.61  thf('183', plain,
% 0.44/0.61      (((((sk_F) != (sk_F))
% 0.44/0.61         | (v1_xboole_0 @ sk_D)
% 0.44/0.61         | (v1_xboole_0 @ sk_C)
% 0.44/0.62         | (v1_xboole_0 @ sk_B)
% 0.44/0.62         | (v1_xboole_0 @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['181', '182'])).
% 0.44/0.62  thf('184', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_A)
% 0.44/0.62         | (v1_xboole_0 @ sk_B)
% 0.44/0.62         | (v1_xboole_0 @ sk_C)
% 0.44/0.62         | (v1_xboole_0 @ sk_D)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['183'])).
% 0.44/0.62  thf('185', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('186', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['184', '185'])).
% 0.44/0.62  thf('187', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('188', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('clc', [status(thm)], ['186', '187'])).
% 0.44/0.62  thf('189', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('190', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_B))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('clc', [status(thm)], ['188', '189'])).
% 0.44/0.62  thf('191', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('192', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          = (sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['190', '191'])).
% 0.44/0.62  thf('193', plain,
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
% 0.44/0.62      inference('split', [status(esa)], ['138'])).
% 0.44/0.62  thf('194', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62          = (sk_E)))),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['153', '192', '193'])).
% 0.44/0.62  thf('195', plain,
% 0.44/0.62      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62         != (sk_E))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['139', '194'])).
% 0.44/0.62  thf('196', plain,
% 0.44/0.62      ((((sk_E) != (sk_E))
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['137', '195'])).
% 0.44/0.62  thf('197', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['196'])).
% 0.44/0.62  thf('198', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('199', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['197', '198'])).
% 0.44/0.62  thf('200', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('201', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.62      inference('clc', [status(thm)], ['199', '200'])).
% 0.44/0.62  thf('202', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('203', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('clc', [status(thm)], ['201', '202'])).
% 0.44/0.62  thf('204', plain, ($false), inference('demod', [status(thm)], ['0', '203'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
