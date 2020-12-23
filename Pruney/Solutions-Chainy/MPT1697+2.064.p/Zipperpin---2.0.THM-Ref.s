%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CzOCVMWK2y

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:03 EST 2020

% Result     : Theorem 28.49s
% Output     : Refutation 28.49s
% Verified   : 
% Statistics : Number of formulae       :  250 (1196 expanded)
%              Number of leaves         :   39 ( 361 expanded)
%              Depth                    :   38
%              Number of atoms          : 3642 (44486 expanded)
%              Number of equality atoms :  133 (1483 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X40 @ X38 @ X37 @ X39 @ X36 @ X41 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X40 @ X38 @ X37 @ X39 @ X36 @ X41 ) @ ( k4_subset_1 @ X40 @ X37 @ X39 ) @ X38 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X40 ) )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X40 @ X38 @ X37 @ X39 @ X36 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X40 @ X37 @ X39 ) @ X38 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ( X35
       != ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 @ X35 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X34 @ X29 @ X33 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) )
       != ( k2_partfun1 @ X30 @ X29 @ X32 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X29 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X29 ) ) )
      | ( ( k2_partfun1 @ X34 @ X29 @ X33 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) )
       != ( k2_partfun1 @ X30 @ X29 @ X32 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_subset_1 @ X17 @ X18 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( ( k2_partfun1 @ X26 @ X27 @ X25 @ X28 )
        = ( k7_relat_1 @ X25 @ X28 ) ) ) ),
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

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X10 ) @ X11 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k7_relat_1 @ sk_E @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('84',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_E ) @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_E ) @ sk_D ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_E ) @ sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('91',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_E ) @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X8 @ X9 )
        = ( k7_relat_1 @ X8 @ ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('93',plain,
    ( ( ( k7_relat_1 @ sk_E @ sk_D )
      = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('95',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('96',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('99',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( ( k2_partfun1 @ X26 @ X27 @ X25 @ X28 )
        = ( k7_relat_1 @ X25 @ X28 ) ) ) ),
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
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('114',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('115',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X10 ) @ X11 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_D ) @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k7_relat_1 @ sk_F @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['109','110'])).

thf('120',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_F ) @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['109','110'])).

thf('124',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_F ) @ sk_C ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_F ) @ sk_C ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('127',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_F ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ X8 @ X9 )
        = ( k7_relat_1 @ X8 @ ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('129',plain,
    ( ( ( k7_relat_1 @ sk_F @ sk_C )
      = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('131',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['109','110'])).

thf('132',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','96','97','98','103','132','133','134','135','136'])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['139'])).

thf('141',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('144',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['139'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('147',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('151',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('152',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('153',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152'])).

thf('154',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['141','153'])).

thf('155',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('157',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('158',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('159',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ( X35
       != ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 @ X35 @ X30 )
        = X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X34 @ X29 @ X33 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) )
       != ( k2_partfun1 @ X30 @ X29 @ X32 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('160',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X29 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X29 ) ) )
      | ( ( k2_partfun1 @ X34 @ X29 @ X33 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) )
       != ( k2_partfun1 @ X30 @ X29 @ X32 @ ( k9_subset_1 @ X31 @ X34 @ X30 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X31 @ X34 @ X30 ) @ X29 @ ( k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32 ) @ X30 )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
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
    inference('sup-',[status(thm)],['158','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('169',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('171',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('173',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('174',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
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
    inference(demod,[status(thm)],['161','162','163','164','165','166','167','168','169','170','171','172','173','174','175','176','177'])).

thf('179',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
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
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['157','179'])).

thf('181',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
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
    inference('sup-',[status(thm)],['156','181'])).

thf('183',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['139'])).

thf('185',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['139'])).

thf('196',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['155','194','195'])).

thf('197',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['140','196'])).

thf('198',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['138','197'])).

thf('199',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','198'])).

thf('200',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','200'])).

thf('202',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    $false ),
    inference(demod,[status(thm)],['0','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CzOCVMWK2y
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 28.49/28.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.49/28.72  % Solved by: fo/fo7.sh
% 28.49/28.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.49/28.72  % done 650 iterations in 28.264s
% 28.49/28.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.49/28.72  % SZS output start Refutation
% 28.49/28.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 28.49/28.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 28.49/28.72  thf(sk_E_type, type, sk_E: $i).
% 28.49/28.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 28.49/28.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.49/28.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 28.49/28.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 28.49/28.72  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 28.49/28.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 28.49/28.72  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 28.49/28.72  thf(sk_C_type, type, sk_C: $i).
% 28.49/28.72  thf(sk_D_type, type, sk_D: $i).
% 28.49/28.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 28.49/28.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 28.49/28.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 28.49/28.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 28.49/28.72  thf(sk_B_type, type, sk_B: $i).
% 28.49/28.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 28.49/28.72  thf(sk_A_type, type, sk_A: $i).
% 28.49/28.72  thf(sk_F_type, type, sk_F: $i).
% 28.49/28.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 28.49/28.72  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 28.49/28.72  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 28.49/28.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 28.49/28.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.49/28.72  thf(t6_tmap_1, conjecture,
% 28.49/28.72    (![A:$i]:
% 28.49/28.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 28.49/28.72       ( ![B:$i]:
% 28.49/28.72         ( ( ~( v1_xboole_0 @ B ) ) =>
% 28.49/28.72           ( ![C:$i]:
% 28.49/28.72             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 28.49/28.72                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.49/28.72               ( ![D:$i]:
% 28.49/28.72                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 28.49/28.72                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.49/28.72                   ( ( r1_subset_1 @ C @ D ) =>
% 28.49/28.72                     ( ![E:$i]:
% 28.49/28.72                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 28.49/28.72                           ( m1_subset_1 @
% 28.49/28.72                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 28.49/28.72                         ( ![F:$i]:
% 28.49/28.72                           ( ( ( v1_funct_1 @ F ) & 
% 28.49/28.72                               ( v1_funct_2 @ F @ D @ B ) & 
% 28.49/28.72                               ( m1_subset_1 @
% 28.49/28.72                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 28.49/28.72                             ( ( ( k2_partfun1 @
% 28.49/28.72                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 28.49/28.72                                 ( k2_partfun1 @
% 28.49/28.72                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 28.49/28.72                               ( ( k2_partfun1 @
% 28.49/28.72                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 28.49/28.72                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 28.49/28.72                                 ( E ) ) & 
% 28.49/28.72                               ( ( k2_partfun1 @
% 28.49/28.72                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 28.49/28.72                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 28.49/28.72                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 28.49/28.72  thf(zf_stmt_0, negated_conjecture,
% 28.49/28.72    (~( ![A:$i]:
% 28.49/28.72        ( ( ~( v1_xboole_0 @ A ) ) =>
% 28.49/28.72          ( ![B:$i]:
% 28.49/28.72            ( ( ~( v1_xboole_0 @ B ) ) =>
% 28.49/28.72              ( ![C:$i]:
% 28.49/28.72                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 28.49/28.72                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.49/28.72                  ( ![D:$i]:
% 28.49/28.72                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 28.49/28.72                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.49/28.72                      ( ( r1_subset_1 @ C @ D ) =>
% 28.49/28.72                        ( ![E:$i]:
% 28.49/28.72                          ( ( ( v1_funct_1 @ E ) & 
% 28.49/28.72                              ( v1_funct_2 @ E @ C @ B ) & 
% 28.49/28.72                              ( m1_subset_1 @
% 28.49/28.72                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 28.49/28.72                            ( ![F:$i]:
% 28.49/28.72                              ( ( ( v1_funct_1 @ F ) & 
% 28.49/28.72                                  ( v1_funct_2 @ F @ D @ B ) & 
% 28.49/28.72                                  ( m1_subset_1 @
% 28.49/28.72                                    F @ 
% 28.49/28.72                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 28.49/28.72                                ( ( ( k2_partfun1 @
% 28.49/28.72                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 28.49/28.72                                    ( k2_partfun1 @
% 28.49/28.72                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 28.49/28.72                                  ( ( k2_partfun1 @
% 28.49/28.72                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 28.49/28.72                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 28.49/28.72                                    ( E ) ) & 
% 28.49/28.72                                  ( ( k2_partfun1 @
% 28.49/28.72                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 28.49/28.72                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 28.49/28.72                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 28.49/28.72    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 28.49/28.72  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('2', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('3', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf(dt_k1_tmap_1, axiom,
% 28.49/28.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 28.49/28.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 28.49/28.72         ( ~( v1_xboole_0 @ C ) ) & 
% 28.49/28.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 28.49/28.72         ( ~( v1_xboole_0 @ D ) ) & 
% 28.49/28.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 28.49/28.72         ( v1_funct_2 @ E @ C @ B ) & 
% 28.49/28.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 28.49/28.72         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 28.49/28.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 28.49/28.72       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 28.49/28.72         ( v1_funct_2 @
% 28.49/28.72           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 28.49/28.72           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 28.49/28.72         ( m1_subset_1 @
% 28.49/28.72           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 28.49/28.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 28.49/28.72  thf('4', plain,
% 28.49/28.72      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 28.49/28.72          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 28.49/28.72          | ~ (v1_funct_1 @ X36)
% 28.49/28.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 28.49/28.72          | (v1_xboole_0 @ X39)
% 28.49/28.72          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X40))
% 28.49/28.72          | (v1_xboole_0 @ X37)
% 28.49/28.72          | (v1_xboole_0 @ X38)
% 28.49/28.72          | (v1_xboole_0 @ X40)
% 28.49/28.72          | ~ (v1_funct_1 @ X41)
% 28.49/28.72          | ~ (v1_funct_2 @ X41 @ X39 @ X38)
% 28.49/28.72          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 28.49/28.72          | (v1_funct_1 @ (k1_tmap_1 @ X40 @ X38 @ X37 @ X39 @ X36 @ X41)))),
% 28.49/28.72      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 28.49/28.72  thf('5', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.49/28.72         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 28.49/28.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 28.49/28.72          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 28.49/28.72          | ~ (v1_funct_1 @ X0)
% 28.49/28.72          | (v1_xboole_0 @ X2)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 28.49/28.72          | (v1_xboole_0 @ X1)
% 28.49/28.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 28.49/28.72          | ~ (v1_funct_1 @ sk_E)
% 28.49/28.72          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 28.49/28.72      inference('sup-', [status(thm)], ['3', '4'])).
% 28.49/28.72  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('8', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.49/28.72         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 28.49/28.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 28.49/28.72          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 28.49/28.72          | ~ (v1_funct_1 @ X0)
% 28.49/28.72          | (v1_xboole_0 @ X2)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 28.49/28.72          | (v1_xboole_0 @ X1)
% 28.49/28.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 28.49/28.72      inference('demod', [status(thm)], ['5', '6', '7'])).
% 28.49/28.72  thf('9', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_D)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (v1_funct_1 @ sk_F)
% 28.49/28.72          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 28.49/28.72          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['2', '8'])).
% 28.49/28.72  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('12', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_D)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 28.49/28.72      inference('demod', [status(thm)], ['9', '10', '11'])).
% 28.49/28.72  thf('13', plain,
% 28.49/28.72      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['1', '12'])).
% 28.49/28.72  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('15', plain,
% 28.49/28.72      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['13', '14'])).
% 28.49/28.72  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('17', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('18', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('19', plain,
% 28.49/28.72      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 28.49/28.72          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 28.49/28.72          | ~ (v1_funct_1 @ X36)
% 28.49/28.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 28.49/28.72          | (v1_xboole_0 @ X39)
% 28.49/28.72          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X40))
% 28.49/28.72          | (v1_xboole_0 @ X37)
% 28.49/28.72          | (v1_xboole_0 @ X38)
% 28.49/28.72          | (v1_xboole_0 @ X40)
% 28.49/28.72          | ~ (v1_funct_1 @ X41)
% 28.49/28.72          | ~ (v1_funct_2 @ X41 @ X39 @ X38)
% 28.49/28.72          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 28.49/28.72          | (v1_funct_2 @ (k1_tmap_1 @ X40 @ X38 @ X37 @ X39 @ X36 @ X41) @ 
% 28.49/28.72             (k4_subset_1 @ X40 @ X37 @ X39) @ X38))),
% 28.49/28.72      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 28.49/28.72  thf('20', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.49/28.72         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 28.49/28.72           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 28.49/28.72          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 28.49/28.72          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 28.49/28.72          | ~ (v1_funct_1 @ X2)
% 28.49/28.72          | (v1_xboole_0 @ X1)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 28.49/28.72          | ~ (v1_funct_1 @ sk_E)
% 28.49/28.72          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 28.49/28.72      inference('sup-', [status(thm)], ['18', '19'])).
% 28.49/28.72  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('23', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.49/28.72         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 28.49/28.72           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 28.49/28.72          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 28.49/28.72          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 28.49/28.72          | ~ (v1_funct_1 @ X2)
% 28.49/28.72          | (v1_xboole_0 @ X1)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 28.49/28.72      inference('demod', [status(thm)], ['20', '21', '22'])).
% 28.49/28.72  thf('24', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_D)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (v1_funct_1 @ sk_F)
% 28.49/28.72          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 28.49/28.72          | (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 28.49/28.72      inference('sup-', [status(thm)], ['17', '23'])).
% 28.49/28.72  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('27', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_D)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 28.49/28.72      inference('demod', [status(thm)], ['24', '25', '26'])).
% 28.49/28.72  thf('28', plain,
% 28.49/28.72      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['16', '27'])).
% 28.49/28.72  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('30', plain,
% 28.49/28.72      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['28', '29'])).
% 28.49/28.72  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('32', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('33', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('34', plain,
% 28.49/28.72      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 28.49/28.72          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 28.49/28.72          | ~ (v1_funct_1 @ X36)
% 28.49/28.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 28.49/28.72          | (v1_xboole_0 @ X39)
% 28.49/28.72          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X40))
% 28.49/28.72          | (v1_xboole_0 @ X37)
% 28.49/28.72          | (v1_xboole_0 @ X38)
% 28.49/28.72          | (v1_xboole_0 @ X40)
% 28.49/28.72          | ~ (v1_funct_1 @ X41)
% 28.49/28.72          | ~ (v1_funct_2 @ X41 @ X39 @ X38)
% 28.49/28.72          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 28.49/28.72          | (m1_subset_1 @ (k1_tmap_1 @ X40 @ X38 @ X37 @ X39 @ X36 @ X41) @ 
% 28.49/28.72             (k1_zfmisc_1 @ 
% 28.49/28.72              (k2_zfmisc_1 @ (k4_subset_1 @ X40 @ X37 @ X39) @ X38))))),
% 28.49/28.72      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 28.49/28.72  thf('35', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.49/28.72         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 28.49/28.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 28.49/28.72          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 28.49/28.72          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 28.49/28.72          | ~ (v1_funct_1 @ X2)
% 28.49/28.72          | (v1_xboole_0 @ X1)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 28.49/28.72          | ~ (v1_funct_1 @ sk_E)
% 28.49/28.72          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 28.49/28.72      inference('sup-', [status(thm)], ['33', '34'])).
% 28.49/28.72  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('38', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.49/28.72         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 28.49/28.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 28.49/28.72          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 28.49/28.72          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 28.49/28.72          | ~ (v1_funct_1 @ X2)
% 28.49/28.72          | (v1_xboole_0 @ X1)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 28.49/28.72      inference('demod', [status(thm)], ['35', '36', '37'])).
% 28.49/28.72  thf('39', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_D)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | ~ (v1_funct_1 @ sk_F)
% 28.49/28.72          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 28.49/28.72          | (m1_subset_1 @ 
% 28.49/28.72             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k1_zfmisc_1 @ 
% 28.49/28.72              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 28.49/28.72      inference('sup-', [status(thm)], ['32', '38'])).
% 28.49/28.72  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('42', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_D)
% 28.49/28.72          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 28.49/28.72          | (v1_xboole_0 @ sk_C)
% 28.49/28.72          | (v1_xboole_0 @ sk_B)
% 28.49/28.72          | (v1_xboole_0 @ X0)
% 28.49/28.72          | (m1_subset_1 @ 
% 28.49/28.72             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k1_zfmisc_1 @ 
% 28.49/28.72              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 28.49/28.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 28.49/28.72  thf('43', plain,
% 28.49/28.72      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72         (k1_zfmisc_1 @ 
% 28.49/28.72          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['31', '42'])).
% 28.49/28.72  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('45', plain,
% 28.49/28.72      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72         (k1_zfmisc_1 @ 
% 28.49/28.72          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['43', '44'])).
% 28.49/28.72  thf(d1_tmap_1, axiom,
% 28.49/28.72    (![A:$i]:
% 28.49/28.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 28.49/28.72       ( ![B:$i]:
% 28.49/28.72         ( ( ~( v1_xboole_0 @ B ) ) =>
% 28.49/28.72           ( ![C:$i]:
% 28.49/28.72             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 28.49/28.72                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.49/28.72               ( ![D:$i]:
% 28.49/28.72                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 28.49/28.72                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.49/28.72                   ( ![E:$i]:
% 28.49/28.72                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 28.49/28.72                         ( m1_subset_1 @
% 28.49/28.72                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 28.49/28.72                       ( ![F:$i]:
% 28.49/28.72                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 28.49/28.72                             ( m1_subset_1 @
% 28.49/28.72                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 28.49/28.72                           ( ( ( k2_partfun1 @
% 28.49/28.72                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 28.49/28.72                               ( k2_partfun1 @
% 28.49/28.72                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 28.49/28.72                             ( ![G:$i]:
% 28.49/28.72                               ( ( ( v1_funct_1 @ G ) & 
% 28.49/28.72                                   ( v1_funct_2 @
% 28.49/28.72                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 28.49/28.72                                   ( m1_subset_1 @
% 28.49/28.72                                     G @ 
% 28.49/28.72                                     ( k1_zfmisc_1 @
% 28.49/28.72                                       ( k2_zfmisc_1 @
% 28.49/28.72                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 28.49/28.72                                 ( ( ( G ) =
% 28.49/28.72                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 28.49/28.72                                   ( ( ( k2_partfun1 @
% 28.49/28.72                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 28.49/28.72                                         C ) =
% 28.49/28.72                                       ( E ) ) & 
% 28.49/28.72                                     ( ( k2_partfun1 @
% 28.49/28.72                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 28.49/28.72                                         D ) =
% 28.49/28.72                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 28.49/28.72  thf('46', plain,
% 28.49/28.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 28.49/28.72         ((v1_xboole_0 @ X29)
% 28.49/28.72          | (v1_xboole_0 @ X30)
% 28.49/28.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | ~ (v1_funct_1 @ X32)
% 28.49/28.72          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 28.49/28.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 28.49/28.72          | ((X35) != (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32))
% 28.49/28.72          | ((k2_partfun1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29 @ X35 @ X34)
% 28.49/28.72              = (X33))
% 28.49/28.72          | ~ (m1_subset_1 @ X35 @ 
% 28.49/28.72               (k1_zfmisc_1 @ 
% 28.49/28.72                (k2_zfmisc_1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29)))
% 28.49/28.72          | ~ (v1_funct_2 @ X35 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29)
% 28.49/28.72          | ~ (v1_funct_1 @ X35)
% 28.49/28.72          | ((k2_partfun1 @ X34 @ X29 @ X33 @ (k9_subset_1 @ X31 @ X34 @ X30))
% 28.49/28.72              != (k2_partfun1 @ X30 @ X29 @ X32 @ 
% 28.49/28.72                  (k9_subset_1 @ X31 @ X34 @ X30)))
% 28.49/28.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X29)))
% 28.49/28.72          | ~ (v1_funct_2 @ X33 @ X34 @ X29)
% 28.49/28.72          | ~ (v1_funct_1 @ X33)
% 28.49/28.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | (v1_xboole_0 @ X34)
% 28.49/28.72          | (v1_xboole_0 @ X31))),
% 28.49/28.72      inference('cnf', [status(esa)], [d1_tmap_1])).
% 28.49/28.72  thf('47', plain,
% 28.49/28.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 28.49/28.72         ((v1_xboole_0 @ X31)
% 28.49/28.72          | (v1_xboole_0 @ X34)
% 28.49/28.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | ~ (v1_funct_1 @ X33)
% 28.49/28.72          | ~ (v1_funct_2 @ X33 @ X34 @ X29)
% 28.49/28.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X29)))
% 28.49/28.72          | ((k2_partfun1 @ X34 @ X29 @ X33 @ (k9_subset_1 @ X31 @ X34 @ X30))
% 28.49/28.72              != (k2_partfun1 @ X30 @ X29 @ X32 @ 
% 28.49/28.72                  (k9_subset_1 @ X31 @ X34 @ X30)))
% 28.49/28.72          | ~ (v1_funct_1 @ (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32))
% 28.49/28.72          | ~ (v1_funct_2 @ (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32) @ 
% 28.49/28.72               (k4_subset_1 @ X31 @ X34 @ X30) @ X29)
% 28.49/28.72          | ~ (m1_subset_1 @ (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32) @ 
% 28.49/28.72               (k1_zfmisc_1 @ 
% 28.49/28.72                (k2_zfmisc_1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29)))
% 28.49/28.72          | ((k2_partfun1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29 @ 
% 28.49/28.72              (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32) @ X34) = (
% 28.49/28.72              X33))
% 28.49/28.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 28.49/28.72          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 28.49/28.72          | ~ (v1_funct_1 @ X32)
% 28.49/28.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | (v1_xboole_0 @ X30)
% 28.49/28.72          | (v1_xboole_0 @ X29))),
% 28.49/28.72      inference('simplify', [status(thm)], ['46'])).
% 28.49/28.72  thf('48', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | ~ (v1_funct_1 @ sk_F)
% 28.49/28.72        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72            = (sk_E))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 28.49/28.72        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 28.49/28.72        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 28.49/28.72        | ~ (v1_funct_1 @ sk_E)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_A))),
% 28.49/28.72      inference('sup-', [status(thm)], ['45', '47'])).
% 28.49/28.72  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('52', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf(redefinition_k9_subset_1, axiom,
% 28.49/28.72    (![A:$i,B:$i,C:$i]:
% 28.49/28.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 28.49/28.72       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 28.49/28.72  thf('54', plain,
% 28.49/28.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 28.49/28.72         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 28.49/28.72          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 28.49/28.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 28.49/28.72  thf('55', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['53', '54'])).
% 28.49/28.72  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf(redefinition_r1_subset_1, axiom,
% 28.49/28.72    (![A:$i,B:$i]:
% 28.49/28.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 28.49/28.72       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 28.49/28.72  thf('57', plain,
% 28.49/28.72      (![X17 : $i, X18 : $i]:
% 28.49/28.72         ((v1_xboole_0 @ X17)
% 28.49/28.72          | (v1_xboole_0 @ X18)
% 28.49/28.72          | (r1_xboole_0 @ X17 @ X18)
% 28.49/28.72          | ~ (r1_subset_1 @ X17 @ X18))),
% 28.49/28.72      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 28.49/28.72  thf('58', plain,
% 28.49/28.72      (((r1_xboole_0 @ sk_C @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C))),
% 28.49/28.72      inference('sup-', [status(thm)], ['56', '57'])).
% 28.49/28.72  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 28.49/28.72      inference('clc', [status(thm)], ['58', '59'])).
% 28.49/28.72  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 28.49/28.72      inference('clc', [status(thm)], ['60', '61'])).
% 28.49/28.72  thf(d7_xboole_0, axiom,
% 28.49/28.72    (![A:$i,B:$i]:
% 28.49/28.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 28.49/28.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 28.49/28.72  thf('63', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i]:
% 28.49/28.72         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 28.49/28.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 28.49/28.72  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['62', '63'])).
% 28.49/28.72  thf('65', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf(redefinition_k2_partfun1, axiom,
% 28.49/28.72    (![A:$i,B:$i,C:$i,D:$i]:
% 28.49/28.72     ( ( ( v1_funct_1 @ C ) & 
% 28.49/28.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.49/28.72       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 28.49/28.72  thf('66', plain,
% 28.49/28.72      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 28.49/28.72          | ~ (v1_funct_1 @ X25)
% 28.49/28.72          | ((k2_partfun1 @ X26 @ X27 @ X25 @ X28) = (k7_relat_1 @ X25 @ X28)))),
% 28.49/28.72      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 28.49/28.72  thf('67', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 28.49/28.72          | ~ (v1_funct_1 @ sk_E))),
% 28.49/28.72      inference('sup-', [status(thm)], ['65', '66'])).
% 28.49/28.72  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('69', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 28.49/28.72      inference('demod', [status(thm)], ['67', '68'])).
% 28.49/28.72  thf('70', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf(cc2_relset_1, axiom,
% 28.49/28.72    (![A:$i,B:$i,C:$i]:
% 28.49/28.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.49/28.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 28.49/28.72  thf('71', plain,
% 28.49/28.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 28.49/28.72         ((v4_relat_1 @ X22 @ X23)
% 28.49/28.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 28.49/28.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.49/28.72  thf('72', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 28.49/28.72      inference('sup-', [status(thm)], ['70', '71'])).
% 28.49/28.72  thf(t209_relat_1, axiom,
% 28.49/28.72    (![A:$i,B:$i]:
% 28.49/28.72     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 28.49/28.72       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 28.49/28.72  thf('73', plain,
% 28.49/28.72      (![X13 : $i, X14 : $i]:
% 28.49/28.72         (((X13) = (k7_relat_1 @ X13 @ X14))
% 28.49/28.72          | ~ (v4_relat_1 @ X13 @ X14)
% 28.49/28.72          | ~ (v1_relat_1 @ X13))),
% 28.49/28.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 28.49/28.72  thf('74', plain,
% 28.49/28.72      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['72', '73'])).
% 28.49/28.72  thf('75', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf(cc1_relset_1, axiom,
% 28.49/28.72    (![A:$i,B:$i,C:$i]:
% 28.49/28.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.49/28.72       ( v1_relat_1 @ C ) ))).
% 28.49/28.72  thf('76', plain,
% 28.49/28.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 28.49/28.72         ((v1_relat_1 @ X19)
% 28.49/28.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 28.49/28.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 28.49/28.72  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 28.49/28.72      inference('sup-', [status(thm)], ['75', '76'])).
% 28.49/28.72  thf('78', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C))),
% 28.49/28.72      inference('demod', [status(thm)], ['74', '77'])).
% 28.49/28.72  thf('79', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 28.49/28.72      inference('clc', [status(thm)], ['60', '61'])).
% 28.49/28.72  thf(t207_relat_1, axiom,
% 28.49/28.72    (![A:$i,B:$i,C:$i]:
% 28.49/28.72     ( ( v1_relat_1 @ C ) =>
% 28.49/28.72       ( ( r1_xboole_0 @ A @ B ) =>
% 28.49/28.72         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 28.49/28.72  thf('80', plain,
% 28.49/28.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 28.49/28.72         (~ (r1_xboole_0 @ X10 @ X11)
% 28.49/28.72          | ~ (v1_relat_1 @ X12)
% 28.49/28.72          | ((k7_relat_1 @ (k7_relat_1 @ X12 @ X10) @ X11) = (k1_xboole_0)))),
% 28.49/28.72      inference('cnf', [status(esa)], [t207_relat_1])).
% 28.49/28.72  thf('81', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_D) = (k1_xboole_0))
% 28.49/28.72          | ~ (v1_relat_1 @ X0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['79', '80'])).
% 28.49/28.72  thf('82', plain,
% 28.49/28.72      ((((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E))),
% 28.49/28.72      inference('sup+', [status(thm)], ['78', '81'])).
% 28.49/28.72  thf('83', plain, ((v1_relat_1 @ sk_E)),
% 28.49/28.72      inference('sup-', [status(thm)], ['75', '76'])).
% 28.49/28.72  thf('84', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['82', '83'])).
% 28.49/28.72  thf(t95_relat_1, axiom,
% 28.49/28.72    (![A:$i,B:$i]:
% 28.49/28.72     ( ( v1_relat_1 @ B ) =>
% 28.49/28.72       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 28.49/28.72         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 28.49/28.72  thf('85', plain,
% 28.49/28.72      (![X15 : $i, X16 : $i]:
% 28.49/28.72         (((k7_relat_1 @ X15 @ X16) != (k1_xboole_0))
% 28.49/28.72          | (r1_xboole_0 @ (k1_relat_1 @ X15) @ X16)
% 28.49/28.72          | ~ (v1_relat_1 @ X15))),
% 28.49/28.72      inference('cnf', [status(esa)], [t95_relat_1])).
% 28.49/28.72  thf('86', plain,
% 28.49/28.72      ((((k1_xboole_0) != (k1_xboole_0))
% 28.49/28.72        | ~ (v1_relat_1 @ sk_E)
% 28.49/28.72        | (r1_xboole_0 @ (k1_relat_1 @ sk_E) @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['84', '85'])).
% 28.49/28.72  thf('87', plain, ((v1_relat_1 @ sk_E)),
% 28.49/28.72      inference('sup-', [status(thm)], ['75', '76'])).
% 28.49/28.72  thf('88', plain,
% 28.49/28.72      ((((k1_xboole_0) != (k1_xboole_0))
% 28.49/28.72        | (r1_xboole_0 @ (k1_relat_1 @ sk_E) @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['86', '87'])).
% 28.49/28.72  thf('89', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_E) @ sk_D)),
% 28.49/28.72      inference('simplify', [status(thm)], ['88'])).
% 28.49/28.72  thf('90', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i]:
% 28.49/28.72         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 28.49/28.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 28.49/28.72  thf('91', plain,
% 28.49/28.72      (((k3_xboole_0 @ (k1_relat_1 @ sk_E) @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['89', '90'])).
% 28.49/28.72  thf(t192_relat_1, axiom,
% 28.49/28.72    (![A:$i,B:$i]:
% 28.49/28.72     ( ( v1_relat_1 @ B ) =>
% 28.49/28.72       ( ( k7_relat_1 @ B @ A ) =
% 28.49/28.72         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 28.49/28.72  thf('92', plain,
% 28.49/28.72      (![X8 : $i, X9 : $i]:
% 28.49/28.72         (((k7_relat_1 @ X8 @ X9)
% 28.49/28.72            = (k7_relat_1 @ X8 @ (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9)))
% 28.49/28.72          | ~ (v1_relat_1 @ X8))),
% 28.49/28.72      inference('cnf', [status(esa)], [t192_relat_1])).
% 28.49/28.72  thf('93', plain,
% 28.49/28.72      ((((k7_relat_1 @ sk_E @ sk_D) = (k7_relat_1 @ sk_E @ k1_xboole_0))
% 28.49/28.72        | ~ (v1_relat_1 @ sk_E))),
% 28.49/28.72      inference('sup+', [status(thm)], ['91', '92'])).
% 28.49/28.72  thf('94', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['82', '83'])).
% 28.49/28.72  thf('95', plain, ((v1_relat_1 @ sk_E)),
% 28.49/28.72      inference('sup-', [status(thm)], ['75', '76'])).
% 28.49/28.72  thf('96', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['93', '94', '95'])).
% 28.49/28.72  thf('97', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['53', '54'])).
% 28.49/28.72  thf('98', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['62', '63'])).
% 28.49/28.72  thf('99', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('100', plain,
% 28.49/28.72      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 28.49/28.72         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 28.49/28.72          | ~ (v1_funct_1 @ X25)
% 28.49/28.72          | ((k2_partfun1 @ X26 @ X27 @ X25 @ X28) = (k7_relat_1 @ X25 @ X28)))),
% 28.49/28.72      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 28.49/28.72  thf('101', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 28.49/28.72          | ~ (v1_funct_1 @ sk_F))),
% 28.49/28.72      inference('sup-', [status(thm)], ['99', '100'])).
% 28.49/28.72  thf('102', plain, ((v1_funct_1 @ sk_F)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('103', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 28.49/28.72      inference('demod', [status(thm)], ['101', '102'])).
% 28.49/28.72  thf('104', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('105', plain,
% 28.49/28.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 28.49/28.72         ((v4_relat_1 @ X22 @ X23)
% 28.49/28.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 28.49/28.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.49/28.72  thf('106', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 28.49/28.72      inference('sup-', [status(thm)], ['104', '105'])).
% 28.49/28.72  thf('107', plain,
% 28.49/28.72      (![X13 : $i, X14 : $i]:
% 28.49/28.72         (((X13) = (k7_relat_1 @ X13 @ X14))
% 28.49/28.72          | ~ (v4_relat_1 @ X13 @ X14)
% 28.49/28.72          | ~ (v1_relat_1 @ X13))),
% 28.49/28.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 28.49/28.72  thf('108', plain,
% 28.49/28.72      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['106', '107'])).
% 28.49/28.72  thf('109', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('110', plain,
% 28.49/28.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 28.49/28.72         ((v1_relat_1 @ X19)
% 28.49/28.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 28.49/28.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 28.49/28.72  thf('111', plain, ((v1_relat_1 @ sk_F)),
% 28.49/28.72      inference('sup-', [status(thm)], ['109', '110'])).
% 28.49/28.72  thf('112', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['108', '111'])).
% 28.49/28.72  thf('113', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 28.49/28.72      inference('clc', [status(thm)], ['60', '61'])).
% 28.49/28.72  thf(symmetry_r1_xboole_0, axiom,
% 28.49/28.72    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 28.49/28.72  thf('114', plain,
% 28.49/28.72      (![X3 : $i, X4 : $i]:
% 28.49/28.72         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 28.49/28.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 28.49/28.72  thf('115', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 28.49/28.72      inference('sup-', [status(thm)], ['113', '114'])).
% 28.49/28.72  thf('116', plain,
% 28.49/28.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 28.49/28.72         (~ (r1_xboole_0 @ X10 @ X11)
% 28.49/28.72          | ~ (v1_relat_1 @ X12)
% 28.49/28.72          | ((k7_relat_1 @ (k7_relat_1 @ X12 @ X10) @ X11) = (k1_xboole_0)))),
% 28.49/28.72      inference('cnf', [status(esa)], [t207_relat_1])).
% 28.49/28.72  thf('117', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_D) @ sk_C) = (k1_xboole_0))
% 28.49/28.72          | ~ (v1_relat_1 @ X0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['115', '116'])).
% 28.49/28.72  thf('118', plain,
% 28.49/28.72      ((((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_F))),
% 28.49/28.72      inference('sup+', [status(thm)], ['112', '117'])).
% 28.49/28.72  thf('119', plain, ((v1_relat_1 @ sk_F)),
% 28.49/28.72      inference('sup-', [status(thm)], ['109', '110'])).
% 28.49/28.72  thf('120', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['118', '119'])).
% 28.49/28.72  thf('121', plain,
% 28.49/28.72      (![X15 : $i, X16 : $i]:
% 28.49/28.72         (((k7_relat_1 @ X15 @ X16) != (k1_xboole_0))
% 28.49/28.72          | (r1_xboole_0 @ (k1_relat_1 @ X15) @ X16)
% 28.49/28.72          | ~ (v1_relat_1 @ X15))),
% 28.49/28.72      inference('cnf', [status(esa)], [t95_relat_1])).
% 28.49/28.72  thf('122', plain,
% 28.49/28.72      ((((k1_xboole_0) != (k1_xboole_0))
% 28.49/28.72        | ~ (v1_relat_1 @ sk_F)
% 28.49/28.72        | (r1_xboole_0 @ (k1_relat_1 @ sk_F) @ sk_C))),
% 28.49/28.72      inference('sup-', [status(thm)], ['120', '121'])).
% 28.49/28.72  thf('123', plain, ((v1_relat_1 @ sk_F)),
% 28.49/28.72      inference('sup-', [status(thm)], ['109', '110'])).
% 28.49/28.72  thf('124', plain,
% 28.49/28.72      ((((k1_xboole_0) != (k1_xboole_0))
% 28.49/28.72        | (r1_xboole_0 @ (k1_relat_1 @ sk_F) @ sk_C))),
% 28.49/28.72      inference('demod', [status(thm)], ['122', '123'])).
% 28.49/28.72  thf('125', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_F) @ sk_C)),
% 28.49/28.72      inference('simplify', [status(thm)], ['124'])).
% 28.49/28.72  thf('126', plain,
% 28.49/28.72      (![X0 : $i, X1 : $i]:
% 28.49/28.72         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 28.49/28.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 28.49/28.72  thf('127', plain,
% 28.49/28.72      (((k3_xboole_0 @ (k1_relat_1 @ sk_F) @ sk_C) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['125', '126'])).
% 28.49/28.72  thf('128', plain,
% 28.49/28.72      (![X8 : $i, X9 : $i]:
% 28.49/28.72         (((k7_relat_1 @ X8 @ X9)
% 28.49/28.72            = (k7_relat_1 @ X8 @ (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9)))
% 28.49/28.72          | ~ (v1_relat_1 @ X8))),
% 28.49/28.72      inference('cnf', [status(esa)], [t192_relat_1])).
% 28.49/28.72  thf('129', plain,
% 28.49/28.72      ((((k7_relat_1 @ sk_F @ sk_C) = (k7_relat_1 @ sk_F @ k1_xboole_0))
% 28.49/28.72        | ~ (v1_relat_1 @ sk_F))),
% 28.49/28.72      inference('sup+', [status(thm)], ['127', '128'])).
% 28.49/28.72  thf('130', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['118', '119'])).
% 28.49/28.72  thf('131', plain, ((v1_relat_1 @ sk_F)),
% 28.49/28.72      inference('sup-', [status(thm)], ['109', '110'])).
% 28.49/28.72  thf('132', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['129', '130', '131'])).
% 28.49/28.72  thf('133', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('134', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('135', plain, ((v1_funct_1 @ sk_E)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('136', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('137', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72            = (sk_E))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ((k1_xboole_0) != (k1_xboole_0))
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_A))),
% 28.49/28.72      inference('demod', [status(thm)],
% 28.49/28.72                ['48', '49', '50', '51', '52', '55', '64', '69', '96', '97', 
% 28.49/28.72                 '98', '103', '132', '133', '134', '135', '136'])).
% 28.49/28.72  thf('138', plain,
% 28.49/28.72      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72            = (sk_E))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify', [status(thm)], ['137'])).
% 28.49/28.72  thf('139', plain,
% 28.49/28.72      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72            != (sk_E))
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            != (sk_F)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('140', plain,
% 28.49/28.72      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72          != (sk_E)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72                = (sk_E))))),
% 28.49/28.72      inference('split', [status(esa)], ['139'])).
% 28.49/28.72  thf('141', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['129', '130', '131'])).
% 28.49/28.72  thf('142', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 28.49/28.72      inference('demod', [status(thm)], ['101', '102'])).
% 28.49/28.72  thf('143', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['53', '54'])).
% 28.49/28.72  thf('144', plain,
% 28.49/28.72      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 28.49/28.72      inference('split', [status(esa)], ['139'])).
% 28.49/28.72  thf('145', plain,
% 28.49/28.72      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 28.49/28.72      inference('sup-', [status(thm)], ['143', '144'])).
% 28.49/28.72  thf('146', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['53', '54'])).
% 28.49/28.72  thf('147', plain,
% 28.49/28.72      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 28.49/28.72          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 28.49/28.72      inference('demod', [status(thm)], ['145', '146'])).
% 28.49/28.72  thf('148', plain,
% 28.49/28.72      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 28.49/28.72          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 28.49/28.72      inference('sup-', [status(thm)], ['142', '147'])).
% 28.49/28.72  thf('149', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['62', '63'])).
% 28.49/28.72  thf('150', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 28.49/28.72      inference('demod', [status(thm)], ['67', '68'])).
% 28.49/28.72  thf('151', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['93', '94', '95'])).
% 28.49/28.72  thf('152', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['62', '63'])).
% 28.49/28.72  thf('153', plain,
% 28.49/28.72      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 28.49/28.72      inference('demod', [status(thm)], ['148', '149', '150', '151', '152'])).
% 28.49/28.72  thf('154', plain,
% 28.49/28.72      ((((k1_xboole_0) != (k1_xboole_0)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 28.49/28.72      inference('sup-', [status(thm)], ['141', '153'])).
% 28.49/28.72  thf('155', plain,
% 28.49/28.72      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 28.49/28.72      inference('simplify', [status(thm)], ['154'])).
% 28.49/28.72  thf('156', plain,
% 28.49/28.72      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['13', '14'])).
% 28.49/28.72  thf('157', plain,
% 28.49/28.72      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['28', '29'])).
% 28.49/28.72  thf('158', plain,
% 28.49/28.72      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72         (k1_zfmisc_1 @ 
% 28.49/28.72          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('demod', [status(thm)], ['43', '44'])).
% 28.49/28.72  thf('159', plain,
% 28.49/28.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 28.49/28.72         ((v1_xboole_0 @ X29)
% 28.49/28.72          | (v1_xboole_0 @ X30)
% 28.49/28.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | ~ (v1_funct_1 @ X32)
% 28.49/28.72          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 28.49/28.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 28.49/28.72          | ((X35) != (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32))
% 28.49/28.72          | ((k2_partfun1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29 @ X35 @ X30)
% 28.49/28.72              = (X32))
% 28.49/28.72          | ~ (m1_subset_1 @ X35 @ 
% 28.49/28.72               (k1_zfmisc_1 @ 
% 28.49/28.72                (k2_zfmisc_1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29)))
% 28.49/28.72          | ~ (v1_funct_2 @ X35 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29)
% 28.49/28.72          | ~ (v1_funct_1 @ X35)
% 28.49/28.72          | ((k2_partfun1 @ X34 @ X29 @ X33 @ (k9_subset_1 @ X31 @ X34 @ X30))
% 28.49/28.72              != (k2_partfun1 @ X30 @ X29 @ X32 @ 
% 28.49/28.72                  (k9_subset_1 @ X31 @ X34 @ X30)))
% 28.49/28.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X29)))
% 28.49/28.72          | ~ (v1_funct_2 @ X33 @ X34 @ X29)
% 28.49/28.72          | ~ (v1_funct_1 @ X33)
% 28.49/28.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | (v1_xboole_0 @ X34)
% 28.49/28.72          | (v1_xboole_0 @ X31))),
% 28.49/28.72      inference('cnf', [status(esa)], [d1_tmap_1])).
% 28.49/28.72  thf('160', plain,
% 28.49/28.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 28.49/28.72         ((v1_xboole_0 @ X31)
% 28.49/28.72          | (v1_xboole_0 @ X34)
% 28.49/28.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | ~ (v1_funct_1 @ X33)
% 28.49/28.72          | ~ (v1_funct_2 @ X33 @ X34 @ X29)
% 28.49/28.72          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X29)))
% 28.49/28.72          | ((k2_partfun1 @ X34 @ X29 @ X33 @ (k9_subset_1 @ X31 @ X34 @ X30))
% 28.49/28.72              != (k2_partfun1 @ X30 @ X29 @ X32 @ 
% 28.49/28.72                  (k9_subset_1 @ X31 @ X34 @ X30)))
% 28.49/28.72          | ~ (v1_funct_1 @ (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32))
% 28.49/28.72          | ~ (v1_funct_2 @ (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32) @ 
% 28.49/28.72               (k4_subset_1 @ X31 @ X34 @ X30) @ X29)
% 28.49/28.72          | ~ (m1_subset_1 @ (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32) @ 
% 28.49/28.72               (k1_zfmisc_1 @ 
% 28.49/28.72                (k2_zfmisc_1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29)))
% 28.49/28.72          | ((k2_partfun1 @ (k4_subset_1 @ X31 @ X34 @ X30) @ X29 @ 
% 28.49/28.72              (k1_tmap_1 @ X31 @ X29 @ X34 @ X30 @ X33 @ X32) @ X30) = (
% 28.49/28.72              X32))
% 28.49/28.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 28.49/28.72          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 28.49/28.72          | ~ (v1_funct_1 @ X32)
% 28.49/28.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 28.49/28.72          | (v1_xboole_0 @ X30)
% 28.49/28.72          | (v1_xboole_0 @ X29))),
% 28.49/28.72      inference('simplify', [status(thm)], ['159'])).
% 28.49/28.72  thf('161', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | ~ (v1_funct_1 @ sk_F)
% 28.49/28.72        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            = (sk_F))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 28.49/28.72            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 28.49/28.72        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 28.49/28.72        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 28.49/28.72        | ~ (v1_funct_1 @ sk_E)
% 28.49/28.72        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_A))),
% 28.49/28.72      inference('sup-', [status(thm)], ['158', '160'])).
% 28.49/28.72  thf('162', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('163', plain, ((v1_funct_1 @ sk_F)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('164', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('165', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('166', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['53', '54'])).
% 28.49/28.72  thf('167', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['62', '63'])).
% 28.49/28.72  thf('168', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 28.49/28.72      inference('demod', [status(thm)], ['67', '68'])).
% 28.49/28.72  thf('169', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['93', '94', '95'])).
% 28.49/28.72  thf('170', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 28.49/28.72      inference('sup-', [status(thm)], ['53', '54'])).
% 28.49/28.72  thf('171', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 28.49/28.72      inference('sup-', [status(thm)], ['62', '63'])).
% 28.49/28.72  thf('172', plain,
% 28.49/28.72      (![X0 : $i]:
% 28.49/28.72         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 28.49/28.72      inference('demod', [status(thm)], ['101', '102'])).
% 28.49/28.72  thf('173', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 28.49/28.72      inference('demod', [status(thm)], ['129', '130', '131'])).
% 28.49/28.72  thf('174', plain,
% 28.49/28.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('175', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('176', plain, ((v1_funct_1 @ sk_E)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('177', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('178', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            = (sk_F))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ((k1_xboole_0) != (k1_xboole_0))
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_A))),
% 28.49/28.72      inference('demod', [status(thm)],
% 28.49/28.72                ['161', '162', '163', '164', '165', '166', '167', '168', 
% 28.49/28.72                 '169', '170', '171', '172', '173', '174', '175', '176', '177'])).
% 28.49/28.72  thf('179', plain,
% 28.49/28.72      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            = (sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify', [status(thm)], ['178'])).
% 28.49/28.72  thf('180', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            = (sk_F))
% 28.49/28.72        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['157', '179'])).
% 28.49/28.72  thf('181', plain,
% 28.49/28.72      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            = (sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify', [status(thm)], ['180'])).
% 28.49/28.72  thf('182', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72            = (sk_F)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['156', '181'])).
% 28.49/28.72  thf('183', plain,
% 28.49/28.72      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72          = (sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify', [status(thm)], ['182'])).
% 28.49/28.72  thf('184', plain,
% 28.49/28.72      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72          != (sk_F)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72                = (sk_F))))),
% 28.49/28.72      inference('split', [status(esa)], ['139'])).
% 28.49/28.72  thf('185', plain,
% 28.49/28.72      (((((sk_F) != (sk_F))
% 28.49/28.72         | (v1_xboole_0 @ sk_D)
% 28.49/28.72         | (v1_xboole_0 @ sk_C)
% 28.49/28.72         | (v1_xboole_0 @ sk_B)
% 28.49/28.72         | (v1_xboole_0 @ sk_A)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72                = (sk_F))))),
% 28.49/28.72      inference('sup-', [status(thm)], ['183', '184'])).
% 28.49/28.72  thf('186', plain,
% 28.49/28.72      ((((v1_xboole_0 @ sk_A)
% 28.49/28.72         | (v1_xboole_0 @ sk_B)
% 28.49/28.72         | (v1_xboole_0 @ sk_C)
% 28.49/28.72         | (v1_xboole_0 @ sk_D)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72                = (sk_F))))),
% 28.49/28.72      inference('simplify', [status(thm)], ['185'])).
% 28.49/28.72  thf('187', plain, (~ (v1_xboole_0 @ sk_D)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('188', plain,
% 28.49/28.72      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72                = (sk_F))))),
% 28.49/28.72      inference('sup-', [status(thm)], ['186', '187'])).
% 28.49/28.72  thf('189', plain, (~ (v1_xboole_0 @ sk_C)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('190', plain,
% 28.49/28.72      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72                = (sk_F))))),
% 28.49/28.72      inference('clc', [status(thm)], ['188', '189'])).
% 28.49/28.72  thf('191', plain, (~ (v1_xboole_0 @ sk_A)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('192', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_B))
% 28.49/28.72         <= (~
% 28.49/28.72             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72                = (sk_F))))),
% 28.49/28.72      inference('clc', [status(thm)], ['190', '191'])).
% 28.49/28.72  thf('193', plain, (~ (v1_xboole_0 @ sk_B)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('194', plain,
% 28.49/28.72      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72          = (sk_F)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['192', '193'])).
% 28.49/28.72  thf('195', plain,
% 28.49/28.72      (~
% 28.49/28.72       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72          = (sk_E))) | 
% 28.49/28.72       ~
% 28.49/28.72       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 28.49/28.72          = (sk_F))) | 
% 28.49/28.72       ~
% 28.49/28.72       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 28.49/28.72          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 28.49/28.72             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 28.49/28.72      inference('split', [status(esa)], ['139'])).
% 28.49/28.72  thf('196', plain,
% 28.49/28.72      (~
% 28.49/28.72       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72          = (sk_E)))),
% 28.49/28.72      inference('sat_resolution*', [status(thm)], ['155', '194', '195'])).
% 28.49/28.72  thf('197', plain,
% 28.49/28.72      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 28.49/28.72         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 28.49/28.72         != (sk_E))),
% 28.49/28.72      inference('simpl_trail', [status(thm)], ['140', '196'])).
% 28.49/28.72  thf('198', plain,
% 28.49/28.72      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | ~ (v1_funct_2 @ 
% 28.49/28.72             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 28.49/28.72             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify_reflect-', [status(thm)], ['138', '197'])).
% 28.49/28.72  thf('199', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 28.49/28.72      inference('sup-', [status(thm)], ['30', '198'])).
% 28.49/28.72  thf('200', plain,
% 28.49/28.72      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify', [status(thm)], ['199'])).
% 28.49/28.72  thf('201', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_D)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_A))),
% 28.49/28.72      inference('sup-', [status(thm)], ['15', '200'])).
% 28.49/28.72  thf('202', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_A)
% 28.49/28.72        | (v1_xboole_0 @ sk_B)
% 28.49/28.72        | (v1_xboole_0 @ sk_C)
% 28.49/28.72        | (v1_xboole_0 @ sk_D))),
% 28.49/28.72      inference('simplify', [status(thm)], ['201'])).
% 28.49/28.72  thf('203', plain, (~ (v1_xboole_0 @ sk_D)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('204', plain,
% 28.49/28.72      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 28.49/28.72      inference('sup-', [status(thm)], ['202', '203'])).
% 28.49/28.72  thf('205', plain, (~ (v1_xboole_0 @ sk_C)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('206', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 28.49/28.72      inference('clc', [status(thm)], ['204', '205'])).
% 28.49/28.72  thf('207', plain, (~ (v1_xboole_0 @ sk_A)),
% 28.49/28.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.49/28.72  thf('208', plain, ((v1_xboole_0 @ sk_B)),
% 28.49/28.72      inference('clc', [status(thm)], ['206', '207'])).
% 28.49/28.72  thf('209', plain, ($false), inference('demod', [status(thm)], ['0', '208'])).
% 28.49/28.72  
% 28.49/28.72  % SZS output end Refutation
% 28.49/28.72  
% 28.49/28.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
