%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XGdDNwCA09

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:53 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  260 (1088 expanded)
%              Number of leaves         :   40 ( 332 expanded)
%              Depth                    :   31
%              Number of atoms          : 3738 (45044 expanded)
%              Number of equality atoms :  121 (1438 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X4 @ X2 @ X3 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X27 @ X28 @ X26 @ X29 )
        = ( k7_relat_1 @ X26 @ X29 ) ) ) ),
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

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['66','67'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('69',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['70','73','76'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X9 @ X10 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['71','72'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
       => ( r1_subset_1 @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ( r1_subset_1 @ X14 @ X13 )
      | ~ ( r1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_subset_1])).

thf('84',plain,
    ( ( r1_subset_1 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_subset_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_subset_1 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['86','87'])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('90',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['70','73','76'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k7_relat_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['71','72'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X27 @ X28 @ X26 @ X29 )
        = ( k7_relat_1 @ X26 @ X29 ) ) ) ),
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
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('119',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('122',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['116','119','122'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('125',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X9 @ X10 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ X0 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['117','118'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('132',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['116','119','122'])).

thf('138',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k7_relat_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['117','118'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['136','141'])).

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
    inference(demod,[status(thm)],['48','49','50','51','52','55','60','81','100','101','106','129','142','143','144','145','146'])).

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
    inference('sup-',[status(thm)],['30','148'])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('155',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['151'])).

thf('156',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('158',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('162',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','99'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('164',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['136','141'])).

thf('165',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164'])).

thf('166',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('168',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('169',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('170',plain,(
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

thf('171',plain,(
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
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
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
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('180',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','99'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('184',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['136','141'])).

thf('185',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
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
    inference(demod,[status(thm)],['172','173','174','175','176','177','178','179','180','181','182','183','184','185','186','187','188'])).

thf('190',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
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
    inference('sup-',[status(thm)],['168','190'])).

thf('192',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
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
      = sk_F ) ),
    inference('sup-',[status(thm)],['167','192'])).

thf('194',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['151'])).

thf('196',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['151'])).

thf('207',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['166','205','206'])).

thf('208',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['152','207'])).

thf('209',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['150','208'])).

thf('210',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','209'])).

thf('211',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    $false ),
    inference(demod,[status(thm)],['0','217'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XGdDNwCA09
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 181 iterations in 0.187s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.65  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.65  thf(t6_tmap_1, conjecture,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.65           ( ![C:$i]:
% 0.44/0.65             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.65                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.65               ( ![D:$i]:
% 0.44/0.65                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.65                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.65                   ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.65                     ( ![E:$i]:
% 0.44/0.65                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.65                           ( m1_subset_1 @
% 0.44/0.65                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.65                         ( ![F:$i]:
% 0.44/0.65                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.65                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.65                               ( m1_subset_1 @
% 0.44/0.65                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.65                             ( ( ( k2_partfun1 @
% 0.44/0.65                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.65                                 ( k2_partfun1 @
% 0.44/0.65                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.65                               ( ( k2_partfun1 @
% 0.44/0.65                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.65                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.65                                 ( E ) ) & 
% 0.44/0.65                               ( ( k2_partfun1 @
% 0.44/0.65                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.65                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.65                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i]:
% 0.44/0.65        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.65          ( ![B:$i]:
% 0.44/0.65            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.65              ( ![C:$i]:
% 0.44/0.65                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.65                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.65                  ( ![D:$i]:
% 0.44/0.65                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.65                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.65                      ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.65                        ( ![E:$i]:
% 0.44/0.65                          ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.65                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.65                              ( m1_subset_1 @
% 0.44/0.65                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.65                            ( ![F:$i]:
% 0.44/0.65                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.65                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.65                                  ( m1_subset_1 @
% 0.44/0.65                                    F @ 
% 0.44/0.65                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.65                                ( ( ( k2_partfun1 @
% 0.44/0.65                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.65                                    ( k2_partfun1 @
% 0.44/0.65                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.65                                  ( ( k2_partfun1 @
% 0.44/0.65                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.65                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.65                                    ( E ) ) & 
% 0.44/0.65                                  ( ( k2_partfun1 @
% 0.44/0.65                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.65                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.65                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.44/0.65  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(dt_k1_tmap_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.65         ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.65         ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.44/0.65         ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.44/0.65         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.65       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.65         ( v1_funct_2 @
% 0.44/0.65           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.65           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.65         ( m1_subset_1 @
% 0.44/0.65           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.65           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.44/0.65          | ~ (v1_funct_1 @ X37)
% 0.44/0.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.44/0.65          | (v1_xboole_0 @ X40)
% 0.44/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.44/0.65          | (v1_xboole_0 @ X38)
% 0.44/0.65          | (v1_xboole_0 @ X39)
% 0.44/0.65          | (v1_xboole_0 @ X41)
% 0.44/0.65          | ~ (v1_funct_1 @ X42)
% 0.44/0.65          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.44/0.65          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.44/0.65          | (v1_funct_1 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42)))),
% 0.44/0.65      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | (v1_xboole_0 @ X2)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.65          | (v1_xboole_0 @ X1)
% 0.44/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.65  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | (v1_xboole_0 @ X2)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.65          | (v1_xboole_0 @ X1)
% 0.44/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.65      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_D)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.65  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_D)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.65      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['1', '12'])).
% 0.44/0.65  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.65  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.44/0.65          | ~ (v1_funct_1 @ X37)
% 0.44/0.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.44/0.65          | (v1_xboole_0 @ X40)
% 0.44/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.44/0.65          | (v1_xboole_0 @ X38)
% 0.44/0.65          | (v1_xboole_0 @ X39)
% 0.44/0.65          | (v1_xboole_0 @ X41)
% 0.44/0.65          | ~ (v1_funct_1 @ X42)
% 0.44/0.65          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.44/0.65          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.44/0.65          | (v1_funct_2 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42) @ 
% 0.44/0.65             (k4_subset_1 @ X41 @ X38 @ X40) @ X39))),
% 0.44/0.65      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.65           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ X2)
% 0.44/0.65          | (v1_xboole_0 @ X1)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.65           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ X2)
% 0.44/0.65          | (v1_xboole_0 @ X1)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.65      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_D)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65          | (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['17', '23'])).
% 0.44/0.65  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_D)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.65      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['16', '27'])).
% 0.44/0.65  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.65  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.65          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.44/0.65          | ~ (v1_funct_1 @ X37)
% 0.44/0.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.44/0.65          | (v1_xboole_0 @ X40)
% 0.44/0.65          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X41))
% 0.44/0.65          | (v1_xboole_0 @ X38)
% 0.44/0.65          | (v1_xboole_0 @ X39)
% 0.44/0.65          | (v1_xboole_0 @ X41)
% 0.44/0.65          | ~ (v1_funct_1 @ X42)
% 0.44/0.65          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.44/0.65          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.44/0.65          | (m1_subset_1 @ (k1_tmap_1 @ X41 @ X39 @ X38 @ X40 @ X37 @ X42) @ 
% 0.44/0.65             (k1_zfmisc_1 @ 
% 0.44/0.65              (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X38 @ X40) @ X39))))),
% 0.44/0.65      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ X2)
% 0.44/0.65          | (v1_xboole_0 @ X1)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.65  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('38', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.65          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ X2)
% 0.44/0.65          | (v1_xboole_0 @ X1)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.65      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_D)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65          | (m1_subset_1 @ 
% 0.44/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k1_zfmisc_1 @ 
% 0.44/0.65              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['32', '38'])).
% 0.44/0.65  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_D)
% 0.44/0.65          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.65          | (v1_xboole_0 @ sk_C)
% 0.44/0.65          | (v1_xboole_0 @ sk_B)
% 0.44/0.65          | (v1_xboole_0 @ X0)
% 0.44/0.65          | (m1_subset_1 @ 
% 0.44/0.65             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k1_zfmisc_1 @ 
% 0.44/0.65              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.65      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k1_zfmisc_1 @ 
% 0.44/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['31', '42'])).
% 0.44/0.65  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k1_zfmisc_1 @ 
% 0.44/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.65  thf(d1_tmap_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.65           ( ![C:$i]:
% 0.44/0.65             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.65                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.65               ( ![D:$i]:
% 0.44/0.65                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.65                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.65                   ( ![E:$i]:
% 0.44/0.65                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.65                         ( m1_subset_1 @
% 0.44/0.65                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.65                       ( ![F:$i]:
% 0.44/0.65                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.65                             ( m1_subset_1 @
% 0.44/0.65                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.65                           ( ( ( k2_partfun1 @
% 0.44/0.65                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.65                               ( k2_partfun1 @
% 0.44/0.65                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.44/0.65                             ( ![G:$i]:
% 0.44/0.65                               ( ( ( v1_funct_1 @ G ) & 
% 0.44/0.65                                   ( v1_funct_2 @
% 0.44/0.65                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.65                                   ( m1_subset_1 @
% 0.44/0.65                                     G @ 
% 0.44/0.65                                     ( k1_zfmisc_1 @
% 0.44/0.65                                       ( k2_zfmisc_1 @
% 0.44/0.65                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.44/0.65                                 ( ( ( G ) =
% 0.44/0.65                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.65                                   ( ( ( k2_partfun1 @
% 0.44/0.65                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.65                                         C ) =
% 0.44/0.65                                       ( E ) ) & 
% 0.44/0.65                                     ( ( k2_partfun1 @
% 0.44/0.65                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.65                                         D ) =
% 0.44/0.65                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X30)
% 0.44/0.65          | (v1_xboole_0 @ X31)
% 0.44/0.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | ~ (v1_funct_1 @ X33)
% 0.44/0.65          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.65          | ((X36) != (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ X36 @ X35)
% 0.44/0.65              = (X34))
% 0.44/0.65          | ~ (m1_subset_1 @ X36 @ 
% 0.44/0.65               (k1_zfmisc_1 @ 
% 0.44/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.65          | ~ (v1_funct_2 @ X36 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.65          | ~ (v1_funct_1 @ X36)
% 0.44/0.65          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.65              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.65                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.65          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.65          | ~ (v1_funct_1 @ X34)
% 0.44/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | (v1_xboole_0 @ X35)
% 0.44/0.65          | (v1_xboole_0 @ X32))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X32)
% 0.44/0.65          | (v1_xboole_0 @ X35)
% 0.44/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | ~ (v1_funct_1 @ X34)
% 0.44/0.65          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.65          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.65              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.65                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.65          | ~ (v1_funct_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.65          | ~ (v1_funct_2 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.65               (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.65          | ~ (m1_subset_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.65               (k1_zfmisc_1 @ 
% 0.44/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ 
% 0.44/0.65              (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ X35) = (
% 0.44/0.65              X34))
% 0.44/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.65          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.65          | ~ (v1_funct_1 @ X33)
% 0.44/0.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | (v1_xboole_0 @ X31)
% 0.44/0.65          | (v1_xboole_0 @ X30))),
% 0.44/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.65        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['45', '47'])).
% 0.44/0.65  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('52', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.65       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.65  thf('54', plain,
% 0.44/0.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.65         (((k9_subset_1 @ X4 @ X2 @ X3) = (k3_xboole_0 @ X2 @ X3))
% 0.44/0.65          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.65  thf('55', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('56', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.65  thf('57', plain,
% 0.44/0.65      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.44/0.65          | ~ (v1_funct_1 @ X26)
% 0.44/0.65          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.65  thf('58', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.65  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('60', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.65  thf('61', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc5_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.65       ( ![C:$i]:
% 0.44/0.65         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.44/0.65             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.65  thf('62', plain,
% 0.44/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.44/0.65          | (v1_partfun1 @ X21 @ X22)
% 0.44/0.65          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.44/0.65          | ~ (v1_funct_1 @ X21)
% 0.44/0.65          | (v1_xboole_0 @ X23))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.65  thf('63', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.65        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.44/0.65  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('65', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('66', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.44/0.65      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.44/0.65  thf('67', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('68', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.44/0.65      inference('clc', [status(thm)], ['66', '67'])).
% 0.44/0.65  thf(d4_partfun1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.65  thf('69', plain,
% 0.44/0.65      (![X24 : $i, X25 : $i]:
% 0.44/0.65         (~ (v1_partfun1 @ X25 @ X24)
% 0.44/0.65          | ((k1_relat_1 @ X25) = (X24))
% 0.44/0.65          | ~ (v4_relat_1 @ X25 @ X24)
% 0.44/0.65          | ~ (v1_relat_1 @ X25))),
% 0.44/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.65  thf('70', plain,
% 0.44/0.65      ((~ (v1_relat_1 @ sk_E)
% 0.44/0.65        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.44/0.65        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.65  thf('71', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc1_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( v1_relat_1 @ C ) ))).
% 0.44/0.65  thf('72', plain,
% 0.44/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X15)
% 0.44/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('73', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.65  thf('74', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(cc2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.65  thf('75', plain,
% 0.44/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X18 @ X19)
% 0.44/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('76', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.44/0.65      inference('sup-', [status(thm)], ['74', '75'])).
% 0.44/0.65  thf('77', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.44/0.65      inference('demod', [status(thm)], ['70', '73', '76'])).
% 0.44/0.65  thf(t192_relat_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ B ) =>
% 0.44/0.65       ( ( k7_relat_1 @ B @ A ) =
% 0.44/0.65         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.44/0.65  thf('78', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i]:
% 0.44/0.65         (((k7_relat_1 @ X9 @ X10)
% 0.44/0.65            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ (k1_relat_1 @ X9) @ X10)))
% 0.44/0.65          | ~ (v1_relat_1 @ X9))),
% 0.44/0.65      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.44/0.65  thf('79', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k7_relat_1 @ sk_E @ X0)
% 0.44/0.65            = (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C @ X0)))
% 0.44/0.65          | ~ (v1_relat_1 @ sk_E))),
% 0.44/0.65      inference('sup+', [status(thm)], ['77', '78'])).
% 0.44/0.65  thf('80', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.65  thf('81', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relat_1 @ sk_E @ X0)
% 0.44/0.65           = (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['79', '80'])).
% 0.44/0.65  thf('82', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(symmetry_r1_subset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.65       ( ( r1_subset_1 @ A @ B ) => ( r1_subset_1 @ B @ A ) ) ))).
% 0.44/0.65  thf('83', plain,
% 0.44/0.65      (![X13 : $i, X14 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X13)
% 0.44/0.65          | (v1_xboole_0 @ X14)
% 0.44/0.65          | (r1_subset_1 @ X14 @ X13)
% 0.44/0.65          | ~ (r1_subset_1 @ X13 @ X14))),
% 0.44/0.65      inference('cnf', [status(esa)], [symmetry_r1_subset_1])).
% 0.44/0.65  thf('84', plain,
% 0.44/0.65      (((r1_subset_1 @ sk_D @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['82', '83'])).
% 0.44/0.65  thf('85', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('86', plain, (((v1_xboole_0 @ sk_C) | (r1_subset_1 @ sk_D @ sk_C))),
% 0.44/0.65      inference('clc', [status(thm)], ['84', '85'])).
% 0.44/0.65  thf('87', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('88', plain, ((r1_subset_1 @ sk_D @ sk_C)),
% 0.44/0.65      inference('clc', [status(thm)], ['86', '87'])).
% 0.44/0.65  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.65       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.65  thf('89', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X11)
% 0.44/0.65          | (v1_xboole_0 @ X12)
% 0.44/0.65          | (r1_xboole_0 @ X11 @ X12)
% 0.44/0.65          | ~ (r1_subset_1 @ X11 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.65  thf('90', plain,
% 0.44/0.65      (((r1_xboole_0 @ sk_D @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.44/0.65  thf('91', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('92', plain, (((v1_xboole_0 @ sk_D) | (r1_xboole_0 @ sk_D @ sk_C))),
% 0.44/0.65      inference('clc', [status(thm)], ['90', '91'])).
% 0.44/0.65  thf('93', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('94', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.44/0.65      inference('clc', [status(thm)], ['92', '93'])).
% 0.44/0.65  thf('95', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.44/0.65      inference('demod', [status(thm)], ['70', '73', '76'])).
% 0.44/0.65  thf(t187_relat_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ A ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.65           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.44/0.65  thf('96', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X7 @ (k1_relat_1 @ X8))
% 0.44/0.65          | ((k7_relat_1 @ X8 @ X7) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X8))),
% 0.44/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.65  thf('97', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.65          | ~ (v1_relat_1 @ sk_E)
% 0.44/0.65          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.44/0.65  thf('98', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.65  thf('99', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.44/0.65          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['97', '98'])).
% 0.44/0.65  thf('100', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['94', '99'])).
% 0.44/0.65  thf('101', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('102', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('103', plain,
% 0.44/0.65      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.44/0.65          | ~ (v1_funct_1 @ X26)
% 0.44/0.65          | ((k2_partfun1 @ X27 @ X28 @ X26 @ X29) = (k7_relat_1 @ X26 @ X29)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.65  thf('104', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.65      inference('sup-', [status(thm)], ['102', '103'])).
% 0.44/0.65  thf('105', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('106', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['104', '105'])).
% 0.44/0.65  thf('107', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('108', plain,
% 0.44/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.44/0.65          | (v1_partfun1 @ X21 @ X22)
% 0.44/0.65          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.44/0.65          | ~ (v1_funct_1 @ X21)
% 0.44/0.65          | (v1_xboole_0 @ X23))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.44/0.65  thf('109', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['107', '108'])).
% 0.44/0.65  thf('110', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('111', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('112', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.44/0.65  thf('113', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('114', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.44/0.65      inference('clc', [status(thm)], ['112', '113'])).
% 0.44/0.65  thf('115', plain,
% 0.44/0.65      (![X24 : $i, X25 : $i]:
% 0.44/0.65         (~ (v1_partfun1 @ X25 @ X24)
% 0.44/0.65          | ((k1_relat_1 @ X25) = (X24))
% 0.44/0.65          | ~ (v4_relat_1 @ X25 @ X24)
% 0.44/0.65          | ~ (v1_relat_1 @ X25))),
% 0.44/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.44/0.65  thf('116', plain,
% 0.44/0.65      ((~ (v1_relat_1 @ sk_F)
% 0.44/0.65        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.44/0.65        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['114', '115'])).
% 0.44/0.65  thf('117', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('118', plain,
% 0.44/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X15)
% 0.44/0.65          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('119', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.65      inference('sup-', [status(thm)], ['117', '118'])).
% 0.44/0.65  thf('120', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('121', plain,
% 0.44/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X18 @ X19)
% 0.44/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('122', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['120', '121'])).
% 0.44/0.65  thf('123', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['116', '119', '122'])).
% 0.44/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.65  thf('124', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.65  thf('125', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i]:
% 0.44/0.65         (((k7_relat_1 @ X9 @ X10)
% 0.44/0.65            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ (k1_relat_1 @ X9) @ X10)))
% 0.44/0.65          | ~ (v1_relat_1 @ X9))),
% 0.44/0.65      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.44/0.65  thf('126', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((k7_relat_1 @ X0 @ X1)
% 0.44/0.65            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.44/0.65          | ~ (v1_relat_1 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['124', '125'])).
% 0.44/0.65  thf('127', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k7_relat_1 @ sk_F @ X0)
% 0.44/0.65            = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ X0 @ sk_D)))
% 0.44/0.65          | ~ (v1_relat_1 @ sk_F))),
% 0.44/0.65      inference('sup+', [status(thm)], ['123', '126'])).
% 0.44/0.65  thf('128', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.65      inference('sup-', [status(thm)], ['117', '118'])).
% 0.44/0.65  thf('129', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relat_1 @ sk_F @ X0)
% 0.44/0.65           = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ X0 @ sk_D)))),
% 0.44/0.65      inference('demod', [status(thm)], ['127', '128'])).
% 0.44/0.65  thf('130', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('131', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X11)
% 0.44/0.65          | (v1_xboole_0 @ X12)
% 0.44/0.65          | (r1_xboole_0 @ X11 @ X12)
% 0.44/0.65          | ~ (r1_subset_1 @ X11 @ X12))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.65  thf('132', plain,
% 0.44/0.65      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['130', '131'])).
% 0.44/0.65  thf('133', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('134', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.65      inference('clc', [status(thm)], ['132', '133'])).
% 0.44/0.65  thf('135', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('136', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.44/0.65      inference('clc', [status(thm)], ['134', '135'])).
% 0.44/0.65  thf('137', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['116', '119', '122'])).
% 0.44/0.65  thf('138', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X7 @ (k1_relat_1 @ X8))
% 0.44/0.65          | ((k7_relat_1 @ X8 @ X7) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X8))),
% 0.44/0.65      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.44/0.65  thf('139', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.65          | ~ (v1_relat_1 @ sk_F)
% 0.44/0.65          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['137', '138'])).
% 0.44/0.65  thf('140', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.65      inference('sup-', [status(thm)], ['117', '118'])).
% 0.44/0.65  thf('141', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.44/0.65          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['139', '140'])).
% 0.44/0.65  thf('142', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['136', '141'])).
% 0.44/0.65  thf('143', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('144', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('145', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('146', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('147', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['48', '49', '50', '51', '52', '55', '60', '81', '100', '101', 
% 0.44/0.65                 '106', '129', '142', '143', '144', '145', '146'])).
% 0.44/0.65  thf('148', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['147'])).
% 0.44/0.65  thf('149', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '148'])).
% 0.44/0.65  thf('150', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65            = (sk_E))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['149'])).
% 0.44/0.65  thf('151', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65            != (sk_E))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            != (sk_F)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('152', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65          != (sk_E)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65                = (sk_E))))),
% 0.44/0.65      inference('split', [status(esa)], ['151'])).
% 0.44/0.65  thf('153', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['104', '105'])).
% 0.44/0.65  thf('154', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('155', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.65      inference('split', [status(esa)], ['151'])).
% 0.44/0.65  thf('156', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['154', '155'])).
% 0.44/0.65  thf('157', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('158', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.44/0.65          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.65      inference('demod', [status(thm)], ['156', '157'])).
% 0.44/0.65  thf('159', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.44/0.65          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['153', '158'])).
% 0.44/0.65  thf('160', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.65  thf('161', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relat_1 @ sk_E @ X0)
% 0.44/0.65           = (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['79', '80'])).
% 0.44/0.65  thf('162', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['94', '99'])).
% 0.44/0.65  thf('163', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relat_1 @ sk_F @ X0)
% 0.44/0.65           = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ X0 @ sk_D)))),
% 0.44/0.65      inference('demod', [status(thm)], ['127', '128'])).
% 0.44/0.65  thf('164', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['136', '141'])).
% 0.44/0.65  thf('165', plain,
% 0.44/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['159', '160', '161', '162', '163', '164'])).
% 0.44/0.65  thf('166', plain,
% 0.44/0.65      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['165'])).
% 0.44/0.65  thf('167', plain,
% 0.44/0.65      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.65  thf('168', plain,
% 0.44/0.65      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.65  thf('169', plain,
% 0.44/0.65      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65         (k1_zfmisc_1 @ 
% 0.44/0.65          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.65  thf('170', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X30)
% 0.44/0.65          | (v1_xboole_0 @ X31)
% 0.44/0.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | ~ (v1_funct_1 @ X33)
% 0.44/0.65          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.65          | ((X36) != (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ X36 @ X31)
% 0.44/0.65              = (X33))
% 0.44/0.65          | ~ (m1_subset_1 @ X36 @ 
% 0.44/0.65               (k1_zfmisc_1 @ 
% 0.44/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.65          | ~ (v1_funct_2 @ X36 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.65          | ~ (v1_funct_1 @ X36)
% 0.44/0.65          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.65              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.65                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.65          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.65          | ~ (v1_funct_1 @ X34)
% 0.44/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | (v1_xboole_0 @ X35)
% 0.44/0.65          | (v1_xboole_0 @ X32))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.65  thf('171', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.65         ((v1_xboole_0 @ X32)
% 0.44/0.65          | (v1_xboole_0 @ X35)
% 0.44/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | ~ (v1_funct_1 @ X34)
% 0.44/0.65          | ~ (v1_funct_2 @ X34 @ X35 @ X30)
% 0.44/0.65          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X30)))
% 0.44/0.65          | ((k2_partfun1 @ X35 @ X30 @ X34 @ (k9_subset_1 @ X32 @ X35 @ X31))
% 0.44/0.65              != (k2_partfun1 @ X31 @ X30 @ X33 @ 
% 0.44/0.65                  (k9_subset_1 @ X32 @ X35 @ X31)))
% 0.44/0.65          | ~ (v1_funct_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33))
% 0.44/0.65          | ~ (v1_funct_2 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.65               (k4_subset_1 @ X32 @ X35 @ X31) @ X30)
% 0.44/0.65          | ~ (m1_subset_1 @ (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ 
% 0.44/0.65               (k1_zfmisc_1 @ 
% 0.44/0.65                (k2_zfmisc_1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30)))
% 0.44/0.65          | ((k2_partfun1 @ (k4_subset_1 @ X32 @ X35 @ X31) @ X30 @ 
% 0.44/0.65              (k1_tmap_1 @ X32 @ X30 @ X35 @ X31 @ X34 @ X33) @ X31) = (
% 0.44/0.65              X33))
% 0.44/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.44/0.65          | ~ (v1_funct_2 @ X33 @ X31 @ X30)
% 0.44/0.65          | ~ (v1_funct_1 @ X33)
% 0.44/0.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.44/0.65          | (v1_xboole_0 @ X31)
% 0.44/0.65          | (v1_xboole_0 @ X30))),
% 0.44/0.65      inference('simplify', [status(thm)], ['170'])).
% 0.44/0.65  thf('172', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.65        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.65            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.65        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.65        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['169', '171'])).
% 0.44/0.65  thf('173', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('174', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('175', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('176', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('177', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('178', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.65  thf('179', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relat_1 @ sk_E @ X0)
% 0.44/0.65           = (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['79', '80'])).
% 0.44/0.65  thf('180', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['94', '99'])).
% 0.44/0.65  thf('181', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.65  thf('182', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['104', '105'])).
% 0.44/0.65  thf('183', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relat_1 @ sk_F @ X0)
% 0.44/0.65           = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ X0 @ sk_D)))),
% 0.44/0.65      inference('demod', [status(thm)], ['127', '128'])).
% 0.44/0.65  thf('184', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['136', '141'])).
% 0.44/0.65  thf('185', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('186', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('187', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('188', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('189', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['172', '173', '174', '175', '176', '177', '178', '179', 
% 0.44/0.65                 '180', '181', '182', '183', '184', '185', '186', '187', '188'])).
% 0.44/0.65  thf('190', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ~ (v1_funct_2 @ 
% 0.44/0.65             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.65             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['189'])).
% 0.44/0.65  thf('191', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['168', '190'])).
% 0.44/0.65  thf('192', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['191'])).
% 0.44/0.65  thf('193', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65            = (sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['167', '192'])).
% 0.44/0.65  thf('194', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          = (sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['193'])).
% 0.44/0.65  thf('195', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          != (sk_F)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('split', [status(esa)], ['151'])).
% 0.44/0.65  thf('196', plain,
% 0.44/0.65      (((((sk_F) != (sk_F))
% 0.44/0.65         | (v1_xboole_0 @ sk_D)
% 0.44/0.65         | (v1_xboole_0 @ sk_C)
% 0.44/0.65         | (v1_xboole_0 @ sk_B)
% 0.44/0.65         | (v1_xboole_0 @ sk_A)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['194', '195'])).
% 0.44/0.65  thf('197', plain,
% 0.44/0.65      ((((v1_xboole_0 @ sk_A)
% 0.44/0.65         | (v1_xboole_0 @ sk_B)
% 0.44/0.65         | (v1_xboole_0 @ sk_C)
% 0.44/0.65         | (v1_xboole_0 @ sk_D)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['196'])).
% 0.44/0.65  thf('198', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('199', plain,
% 0.44/0.65      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['197', '198'])).
% 0.44/0.65  thf('200', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('201', plain,
% 0.44/0.65      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('clc', [status(thm)], ['199', '200'])).
% 0.44/0.65  thf('202', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('203', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_B))
% 0.44/0.65         <= (~
% 0.44/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65                = (sk_F))))),
% 0.44/0.65      inference('clc', [status(thm)], ['201', '202'])).
% 0.44/0.65  thf('204', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('205', plain,
% 0.44/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          = (sk_F)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['203', '204'])).
% 0.44/0.65  thf('206', plain,
% 0.44/0.65      (~
% 0.44/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65          = (sk_E))) | 
% 0.44/0.65       ~
% 0.44/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.65          = (sk_F))) | 
% 0.44/0.65       ~
% 0.44/0.65       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.65          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.65             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.65      inference('split', [status(esa)], ['151'])).
% 0.44/0.65  thf('207', plain,
% 0.44/0.65      (~
% 0.44/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65          = (sk_E)))),
% 0.44/0.65      inference('sat_resolution*', [status(thm)], ['166', '205', '206'])).
% 0.44/0.65  thf('208', plain,
% 0.44/0.65      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.65         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.65         != (sk_E))),
% 0.44/0.65      inference('simpl_trail', [status(thm)], ['152', '207'])).
% 0.44/0.65  thf('209', plain,
% 0.44/0.65      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['150', '208'])).
% 0.44/0.65  thf('210', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_D)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['15', '209'])).
% 0.44/0.65  thf('211', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_A)
% 0.44/0.65        | (v1_xboole_0 @ sk_B)
% 0.44/0.65        | (v1_xboole_0 @ sk_C)
% 0.44/0.65        | (v1_xboole_0 @ sk_D))),
% 0.44/0.65      inference('simplify', [status(thm)], ['210'])).
% 0.44/0.65  thf('212', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('213', plain,
% 0.44/0.65      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['211', '212'])).
% 0.44/0.65  thf('214', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('215', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('clc', [status(thm)], ['213', '214'])).
% 0.44/0.65  thf('216', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('217', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.65      inference('clc', [status(thm)], ['215', '216'])).
% 0.44/0.65  thf('218', plain, ($false), inference('demod', [status(thm)], ['0', '217'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
