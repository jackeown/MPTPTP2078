%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P5xkc62APH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:00 EST 2020

% Result     : Theorem 42.23s
% Output     : Refutation 42.23s
% Verified   : 
% Statistics : Number of formulae       :  258 ( 941 expanded)
%              Number of leaves         :   44 ( 293 expanded)
%              Depth                    :   31
%              Number of atoms          : 3673 (35673 expanded)
%              Number of equality atoms :  117 (1141 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_subset_1 @ X18 @ X19 ) ) ),
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

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k3_xboole_0 @ X3 @ X5 )
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('74',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('76',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_partfun1 @ sk_E @ sk_C_1 ),
    inference(clc,[status(thm)],['90','91'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('93',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('96',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('97',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('99',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('100',plain,(
    v4_relat_1 @ sk_E @ sk_C_1 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C_1 ),
    inference(demod,[status(thm)],['94','97','100'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k7_relat_1 @ X17 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['95','96'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
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
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('109',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('115',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('127',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('130',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['124','127','130'])).

thf('132',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k7_relat_1 @ X17 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','106','107','108','113','136','137','138','139','140'])).

thf('142',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
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
    inference('sup-',[status(thm)],['30','142'])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('149',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['145'])).

thf('150',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('152',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('153',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('154',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['147','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('157',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','105'])).

thf('158',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','135'])).

thf('159',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('162',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('163',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('164',plain,(
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

thf('165',plain,(
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
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
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
    inference('sup-',[status(thm)],['163','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('172',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('174',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','105'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('176',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('178',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','135'])).

thf('179',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
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
    inference(demod,[status(thm)],['166','167','168','169','170','171','172','173','174','175','176','177','178','179','180','181','182'])).

thf('184',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
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
    inference('sup-',[status(thm)],['162','184'])).

thf('186',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
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
    inference('sup-',[status(thm)],['161','186'])).

thf('188',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['145'])).

thf('190',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['145'])).

thf('201',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['160','199','200'])).

thf('202',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['146','201'])).

thf('203',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['144','202'])).

thf('204',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','203'])).

thf('205',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    $false ),
    inference(demod,[status(thm)],['0','211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P5xkc62APH
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 42.23/42.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 42.23/42.47  % Solved by: fo/fo7.sh
% 42.23/42.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.23/42.47  % done 25527 iterations in 42.005s
% 42.23/42.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 42.23/42.47  % SZS output start Refutation
% 42.23/42.47  thf(sk_A_type, type, sk_A: $i).
% 42.23/42.47  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 42.23/42.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 42.23/42.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 42.23/42.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 42.23/42.47  thf(sk_E_type, type, sk_E: $i).
% 42.23/42.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 42.23/42.47  thf(sk_B_type, type, sk_B: $i > $i).
% 42.23/42.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 42.23/42.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 42.23/42.47  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 42.23/42.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 42.23/42.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 42.23/42.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 42.23/42.47  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 42.23/42.47  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 42.23/42.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 42.23/42.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 42.23/42.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 42.23/42.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.23/42.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 42.23/42.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 42.23/42.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 42.23/42.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 42.23/42.47  thf(sk_F_type, type, sk_F: $i).
% 42.23/42.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 42.23/42.47  thf(sk_D_type, type, sk_D: $i).
% 42.23/42.47  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 42.23/42.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 42.23/42.47  thf(t6_tmap_1, conjecture,
% 42.23/42.47    (![A:$i]:
% 42.23/42.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 42.23/42.47       ( ![B:$i]:
% 42.23/42.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 42.23/42.47           ( ![C:$i]:
% 42.23/42.47             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 42.23/42.47                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.23/42.47               ( ![D:$i]:
% 42.23/42.47                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 42.23/42.47                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.23/42.47                   ( ( r1_subset_1 @ C @ D ) =>
% 42.23/42.47                     ( ![E:$i]:
% 42.23/42.47                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 42.23/42.47                           ( m1_subset_1 @
% 42.23/42.47                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 42.23/42.47                         ( ![F:$i]:
% 42.23/42.47                           ( ( ( v1_funct_1 @ F ) & 
% 42.23/42.47                               ( v1_funct_2 @ F @ D @ B ) & 
% 42.23/42.47                               ( m1_subset_1 @
% 42.23/42.47                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 42.23/42.47                             ( ( ( k2_partfun1 @
% 42.23/42.47                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 42.23/42.47                                 ( k2_partfun1 @
% 42.23/42.47                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 42.23/42.47                               ( ( k2_partfun1 @
% 42.23/42.47                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 42.23/42.47                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 42.23/42.47                                 ( E ) ) & 
% 42.23/42.47                               ( ( k2_partfun1 @
% 42.23/42.47                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 42.23/42.47                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 42.23/42.47                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 42.23/42.47  thf(zf_stmt_0, negated_conjecture,
% 42.23/42.47    (~( ![A:$i]:
% 42.23/42.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 42.23/42.47          ( ![B:$i]:
% 42.23/42.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 42.23/42.47              ( ![C:$i]:
% 42.23/42.47                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 42.23/42.47                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.23/42.47                  ( ![D:$i]:
% 42.23/42.47                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 42.23/42.47                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.23/42.47                      ( ( r1_subset_1 @ C @ D ) =>
% 42.23/42.47                        ( ![E:$i]:
% 42.23/42.47                          ( ( ( v1_funct_1 @ E ) & 
% 42.23/42.47                              ( v1_funct_2 @ E @ C @ B ) & 
% 42.23/42.47                              ( m1_subset_1 @
% 42.23/42.47                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 42.23/42.47                            ( ![F:$i]:
% 42.23/42.47                              ( ( ( v1_funct_1 @ F ) & 
% 42.23/42.47                                  ( v1_funct_2 @ F @ D @ B ) & 
% 42.23/42.47                                  ( m1_subset_1 @
% 42.23/42.47                                    F @ 
% 42.23/42.47                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 42.23/42.47                                ( ( ( k2_partfun1 @
% 42.23/42.47                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 42.23/42.47                                    ( k2_partfun1 @
% 42.23/42.47                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 42.23/42.47                                  ( ( k2_partfun1 @
% 42.23/42.47                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 42.23/42.47                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 42.23/42.47                                    ( E ) ) & 
% 42.23/42.47                                  ( ( k2_partfun1 @
% 42.23/42.47                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 42.23/42.47                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 42.23/42.47                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 42.23/42.47    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 42.23/42.47  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('2', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('3', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(dt_k1_tmap_1, axiom,
% 42.23/42.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 42.23/42.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 42.23/42.47         ( ~( v1_xboole_0 @ C ) ) & 
% 42.23/42.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 42.23/42.47         ( ~( v1_xboole_0 @ D ) ) & 
% 42.23/42.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 42.23/42.47         ( v1_funct_2 @ E @ C @ B ) & 
% 42.23/42.47         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 42.23/42.47         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 42.23/42.47         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 42.23/42.47       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 42.23/42.47         ( v1_funct_2 @
% 42.23/42.47           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 42.23/42.47           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 42.23/42.47         ( m1_subset_1 @
% 42.23/42.47           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 42.23/42.47           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 42.23/42.47  thf('4', plain,
% 42.23/42.47      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 42.23/42.47          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 42.23/42.47          | ~ (v1_funct_1 @ X42)
% 42.23/42.47          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 42.23/42.47          | (v1_xboole_0 @ X45)
% 42.23/42.47          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 42.23/42.47          | (v1_xboole_0 @ X43)
% 42.23/42.47          | (v1_xboole_0 @ X44)
% 42.23/42.47          | (v1_xboole_0 @ X46)
% 42.23/42.47          | ~ (v1_funct_1 @ X47)
% 42.23/42.47          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 42.23/42.47          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 42.23/42.47          | (v1_funct_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47)))),
% 42.23/42.47      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 42.23/42.47  thf('5', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.23/42.47         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 42.23/42.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 42.23/42.47          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 42.23/42.47          | ~ (v1_funct_1 @ X0)
% 42.23/42.47          | (v1_xboole_0 @ X2)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 42.23/42.47          | (v1_xboole_0 @ X1)
% 42.23/42.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 42.23/42.47          | ~ (v1_funct_1 @ sk_E)
% 42.23/42.47          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['3', '4'])).
% 42.23/42.47  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('8', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.23/42.47         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 42.23/42.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 42.23/42.47          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 42.23/42.47          | ~ (v1_funct_1 @ X0)
% 42.23/42.47          | (v1_xboole_0 @ X2)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 42.23/42.47          | (v1_xboole_0 @ X1)
% 42.23/42.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 42.23/42.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 42.23/42.47  thf('9', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_D)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (v1_funct_1 @ sk_F)
% 42.23/42.47          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 42.23/42.47          | (v1_funct_1 @ 
% 42.23/42.47             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 42.23/42.47      inference('sup-', [status(thm)], ['2', '8'])).
% 42.23/42.47  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('12', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_D)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | (v1_funct_1 @ 
% 42.23/42.47             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 42.23/42.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 42.23/42.47  thf('13', plain,
% 42.23/42.47      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.47        | (v1_xboole_0 @ sk_D))),
% 42.23/42.47      inference('sup-', [status(thm)], ['1', '12'])).
% 42.23/42.47  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('15', plain,
% 42.23/42.47      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_D))),
% 42.23/42.47      inference('demod', [status(thm)], ['13', '14'])).
% 42.23/42.47  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('17', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('18', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('19', plain,
% 42.23/42.47      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 42.23/42.47          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 42.23/42.47          | ~ (v1_funct_1 @ X42)
% 42.23/42.47          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 42.23/42.47          | (v1_xboole_0 @ X45)
% 42.23/42.47          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 42.23/42.47          | (v1_xboole_0 @ X43)
% 42.23/42.47          | (v1_xboole_0 @ X44)
% 42.23/42.47          | (v1_xboole_0 @ X46)
% 42.23/42.47          | ~ (v1_funct_1 @ X47)
% 42.23/42.47          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 42.23/42.47          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 42.23/42.47          | (v1_funct_2 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 42.23/42.47             (k4_subset_1 @ X46 @ X43 @ X45) @ X44))),
% 42.23/42.47      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 42.23/42.47  thf('20', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.23/42.47         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 42.23/42.47           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 42.23/42.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 42.23/42.47          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 42.23/42.47          | ~ (v1_funct_1 @ X2)
% 42.23/42.47          | (v1_xboole_0 @ X1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 42.23/42.47          | ~ (v1_funct_1 @ sk_E)
% 42.23/42.47          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['18', '19'])).
% 42.23/42.47  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('23', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.23/42.47         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 42.23/42.47           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 42.23/42.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 42.23/42.47          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 42.23/42.47          | ~ (v1_funct_1 @ X2)
% 42.23/42.47          | (v1_xboole_0 @ X1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 42.23/42.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 42.23/42.47  thf('24', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_D)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (v1_funct_1 @ sk_F)
% 42.23/42.47          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 42.23/42.47          | (v1_funct_2 @ 
% 42.23/42.47             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['17', '23'])).
% 42.23/42.47  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('27', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_D)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | (v1_funct_2 @ 
% 42.23/42.47             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 42.23/42.47      inference('demod', [status(thm)], ['24', '25', '26'])).
% 42.23/42.47  thf('28', plain,
% 42.23/42.47      (((v1_funct_2 @ 
% 42.23/42.47         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.47        | (v1_xboole_0 @ sk_D))),
% 42.23/42.47      inference('sup-', [status(thm)], ['16', '27'])).
% 42.23/42.47  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('30', plain,
% 42.23/42.47      (((v1_funct_2 @ 
% 42.23/42.47         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_D))),
% 42.23/42.47      inference('demod', [status(thm)], ['28', '29'])).
% 42.23/42.47  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('32', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('33', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('34', plain,
% 42.23/42.47      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 42.23/42.47          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 42.23/42.47          | ~ (v1_funct_1 @ X42)
% 42.23/42.47          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 42.23/42.47          | (v1_xboole_0 @ X45)
% 42.23/42.47          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 42.23/42.47          | (v1_xboole_0 @ X43)
% 42.23/42.47          | (v1_xboole_0 @ X44)
% 42.23/42.47          | (v1_xboole_0 @ X46)
% 42.23/42.47          | ~ (v1_funct_1 @ X47)
% 42.23/42.47          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 42.23/42.47          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 42.23/42.47          | (m1_subset_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 42.23/42.47             (k1_zfmisc_1 @ 
% 42.23/42.47              (k2_zfmisc_1 @ (k4_subset_1 @ X46 @ X43 @ X45) @ X44))))),
% 42.23/42.47      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 42.23/42.47  thf('35', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.23/42.47         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 42.23/42.47           (k1_zfmisc_1 @ 
% 42.23/42.47            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 42.23/42.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 42.23/42.47          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 42.23/42.47          | ~ (v1_funct_1 @ X2)
% 42.23/42.47          | (v1_xboole_0 @ X1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 42.23/42.47          | ~ (v1_funct_1 @ sk_E)
% 42.23/42.47          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['33', '34'])).
% 42.23/42.47  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('38', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.23/42.47         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 42.23/42.47           (k1_zfmisc_1 @ 
% 42.23/42.47            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 42.23/42.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 42.23/42.47          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 42.23/42.47          | ~ (v1_funct_1 @ X2)
% 42.23/42.47          | (v1_xboole_0 @ X1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 42.23/42.47      inference('demod', [status(thm)], ['35', '36', '37'])).
% 42.23/42.47  thf('39', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_D)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (v1_funct_1 @ sk_F)
% 42.23/42.47          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 42.23/42.47          | (m1_subset_1 @ 
% 42.23/42.47             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47             (k1_zfmisc_1 @ 
% 42.23/42.47              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 42.23/42.47      inference('sup-', [status(thm)], ['32', '38'])).
% 42.23/42.47  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('42', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_D)
% 42.23/42.47          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 42.23/42.47          | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47          | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47          | (v1_xboole_0 @ X0)
% 42.23/42.47          | (m1_subset_1 @ 
% 42.23/42.47             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47             (k1_zfmisc_1 @ 
% 42.23/42.47              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 42.23/42.47      inference('demod', [status(thm)], ['39', '40', '41'])).
% 42.23/42.47  thf('43', plain,
% 42.23/42.47      (((m1_subset_1 @ 
% 42.23/42.47         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47         (k1_zfmisc_1 @ 
% 42.23/42.47          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.47        | (v1_xboole_0 @ sk_D))),
% 42.23/42.47      inference('sup-', [status(thm)], ['31', '42'])).
% 42.23/42.47  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('45', plain,
% 42.23/42.47      (((m1_subset_1 @ 
% 42.23/42.47         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47         (k1_zfmisc_1 @ 
% 42.23/42.47          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_D))),
% 42.23/42.47      inference('demod', [status(thm)], ['43', '44'])).
% 42.23/42.47  thf(d1_tmap_1, axiom,
% 42.23/42.47    (![A:$i]:
% 42.23/42.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 42.23/42.47       ( ![B:$i]:
% 42.23/42.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 42.23/42.47           ( ![C:$i]:
% 42.23/42.47             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 42.23/42.47                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.23/42.47               ( ![D:$i]:
% 42.23/42.47                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 42.23/42.47                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 42.23/42.47                   ( ![E:$i]:
% 42.23/42.47                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 42.23/42.47                         ( m1_subset_1 @
% 42.23/42.47                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 42.23/42.47                       ( ![F:$i]:
% 42.23/42.47                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 42.23/42.47                             ( m1_subset_1 @
% 42.23/42.47                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 42.23/42.47                           ( ( ( k2_partfun1 @
% 42.23/42.47                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 42.23/42.47                               ( k2_partfun1 @
% 42.23/42.47                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 42.23/42.47                             ( ![G:$i]:
% 42.23/42.47                               ( ( ( v1_funct_1 @ G ) & 
% 42.23/42.47                                   ( v1_funct_2 @
% 42.23/42.47                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 42.23/42.47                                   ( m1_subset_1 @
% 42.23/42.47                                     G @ 
% 42.23/42.47                                     ( k1_zfmisc_1 @
% 42.23/42.47                                       ( k2_zfmisc_1 @
% 42.23/42.47                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 42.23/42.47                                 ( ( ( G ) =
% 42.23/42.47                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 42.23/42.47                                   ( ( ( k2_partfun1 @
% 42.23/42.47                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 42.23/42.47                                         C ) =
% 42.23/42.47                                       ( E ) ) & 
% 42.23/42.47                                     ( ( k2_partfun1 @
% 42.23/42.47                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 42.23/42.47                                         D ) =
% 42.23/42.47                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 42.23/42.47  thf('46', plain,
% 42.23/42.47      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 42.23/42.47         ((v1_xboole_0 @ X35)
% 42.23/42.47          | (v1_xboole_0 @ X36)
% 42.23/42.47          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 42.23/42.47          | ~ (v1_funct_1 @ X38)
% 42.23/42.47          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 42.23/42.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 42.23/42.47          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 42.23/42.47          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X40)
% 42.23/42.47              = (X39))
% 42.23/42.47          | ~ (m1_subset_1 @ X41 @ 
% 42.23/42.47               (k1_zfmisc_1 @ 
% 42.23/42.47                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 42.23/42.47          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 42.23/42.47          | ~ (v1_funct_1 @ X41)
% 42.23/42.47          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 42.23/42.47              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 42.23/42.47                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 42.23/42.47          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 42.23/42.47          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 42.23/42.47          | ~ (v1_funct_1 @ X39)
% 42.23/42.47          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 42.23/42.47          | (v1_xboole_0 @ X40)
% 42.23/42.47          | (v1_xboole_0 @ X37))),
% 42.23/42.47      inference('cnf', [status(esa)], [d1_tmap_1])).
% 42.23/42.47  thf('47', plain,
% 42.23/42.47      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 42.23/42.47         ((v1_xboole_0 @ X37)
% 42.23/42.47          | (v1_xboole_0 @ X40)
% 42.23/42.47          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 42.23/42.47          | ~ (v1_funct_1 @ X39)
% 42.23/42.47          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 42.23/42.47          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 42.23/42.47          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 42.23/42.47              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 42.23/42.47                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 42.23/42.47          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 42.23/42.47          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 42.23/42.47               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 42.23/42.47          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 42.23/42.47               (k1_zfmisc_1 @ 
% 42.23/42.47                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 42.23/42.47          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 42.23/42.47              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X40) = (
% 42.23/42.47              X39))
% 42.23/42.47          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 42.23/42.47          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 42.23/42.47          | ~ (v1_funct_1 @ X38)
% 42.23/42.47          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 42.23/42.47          | (v1_xboole_0 @ X36)
% 42.23/42.47          | (v1_xboole_0 @ X35))),
% 42.23/42.47      inference('simplify', [status(thm)], ['46'])).
% 42.23/42.47  thf('48', plain,
% 42.23/42.47      (((v1_xboole_0 @ sk_D)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_A)
% 42.23/42.47        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_D)
% 42.23/42.47        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.47        | ~ (v1_funct_1 @ sk_F)
% 42.23/42.47        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 42.23/42.47        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 42.23/42.47        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.47            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.47            = (sk_E))
% 42.23/42.47        | ~ (v1_funct_2 @ 
% 42.23/42.47             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.47             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.47        | ~ (v1_funct_1 @ 
% 42.23/42.47             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.47        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.47            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.47            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.47                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 42.23/42.47        | ~ (m1_subset_1 @ sk_E @ 
% 42.23/42.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 42.23/42.47        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 42.23/42.47        | ~ (v1_funct_1 @ sk_E)
% 42.23/42.47        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.47        | (v1_xboole_0 @ sk_A))),
% 42.23/42.47      inference('sup-', [status(thm)], ['45', '47'])).
% 42.23/42.47  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('52', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(redefinition_k9_subset_1, axiom,
% 42.23/42.47    (![A:$i,B:$i,C:$i]:
% 42.23/42.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 42.23/42.47       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 42.23/42.47  thf('54', plain,
% 42.23/42.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 42.23/42.47         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 42.23/42.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 42.23/42.47      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 42.23/42.47  thf('55', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 42.23/42.47      inference('sup-', [status(thm)], ['53', '54'])).
% 42.23/42.47  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(redefinition_r1_subset_1, axiom,
% 42.23/42.47    (![A:$i,B:$i]:
% 42.23/42.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 42.23/42.47       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 42.23/42.47  thf('57', plain,
% 42.23/42.47      (![X18 : $i, X19 : $i]:
% 42.23/42.47         ((v1_xboole_0 @ X18)
% 42.23/42.47          | (v1_xboole_0 @ X19)
% 42.23/42.47          | (r1_xboole_0 @ X18 @ X19)
% 42.23/42.47          | ~ (r1_subset_1 @ X18 @ X19))),
% 42.23/42.47      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 42.23/42.47  thf('58', plain,
% 42.23/42.47      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 42.23/42.47        | (v1_xboole_0 @ sk_D)
% 42.23/42.47        | (v1_xboole_0 @ sk_C_1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['56', '57'])).
% 42.23/42.47  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 42.23/42.47      inference('clc', [status(thm)], ['58', '59'])).
% 42.23/42.47  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 42.23/42.47      inference('clc', [status(thm)], ['60', '61'])).
% 42.23/42.47  thf(d7_xboole_0, axiom,
% 42.23/42.47    (![A:$i,B:$i]:
% 42.23/42.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 42.23/42.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 42.23/42.47  thf('63', plain,
% 42.23/42.47      (![X3 : $i, X4 : $i]:
% 42.23/42.47         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 42.23/42.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 42.23/42.47  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 42.23/42.47      inference('sup-', [status(thm)], ['62', '63'])).
% 42.23/42.47  thf('65', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(redefinition_k2_partfun1, axiom,
% 42.23/42.47    (![A:$i,B:$i,C:$i,D:$i]:
% 42.23/42.47     ( ( ( v1_funct_1 @ C ) & 
% 42.23/42.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 42.23/42.47       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 42.23/42.47  thf('66', plain,
% 42.23/42.47      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 42.23/42.47          | ~ (v1_funct_1 @ X31)
% 42.23/42.47          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 42.23/42.47      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 42.23/42.47  thf('67', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 42.23/42.47            = (k7_relat_1 @ sk_E @ X0))
% 42.23/42.47          | ~ (v1_funct_1 @ sk_E))),
% 42.23/42.47      inference('sup-', [status(thm)], ['65', '66'])).
% 42.23/42.47  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('69', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 42.23/42.47           = (k7_relat_1 @ sk_E @ X0))),
% 42.23/42.47      inference('demod', [status(thm)], ['67', '68'])).
% 42.23/42.47  thf(t2_boole, axiom,
% 42.23/42.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 42.23/42.47  thf('70', plain,
% 42.23/42.47      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.47      inference('cnf', [status(esa)], [t2_boole])).
% 42.23/42.47  thf('71', plain,
% 42.23/42.47      (![X3 : $i, X5 : $i]:
% 42.23/42.47         ((r1_xboole_0 @ X3 @ X5) | ((k3_xboole_0 @ X3 @ X5) != (k1_xboole_0)))),
% 42.23/42.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 42.23/42.47  thf('72', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 42.23/42.47      inference('sup-', [status(thm)], ['70', '71'])).
% 42.23/42.47  thf('73', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 42.23/42.47      inference('simplify', [status(thm)], ['72'])).
% 42.23/42.47  thf(d1_xboole_0, axiom,
% 42.23/42.47    (![A:$i]:
% 42.23/42.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 42.23/42.47  thf('74', plain,
% 42.23/42.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 42.23/42.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 42.23/42.47  thf('75', plain,
% 42.23/42.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 42.23/42.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 42.23/42.47  thf(t3_xboole_0, axiom,
% 42.23/42.47    (![A:$i,B:$i]:
% 42.23/42.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 42.23/42.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 42.23/42.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 42.23/42.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 42.23/42.47  thf('76', plain,
% 42.23/42.47      (![X6 : $i, X8 : $i, X9 : $i]:
% 42.23/42.47         (~ (r2_hidden @ X8 @ X6)
% 42.23/42.47          | ~ (r2_hidden @ X8 @ X9)
% 42.23/42.47          | ~ (r1_xboole_0 @ X6 @ X9))),
% 42.23/42.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.23/42.47  thf('77', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i]:
% 42.23/42.47         ((v1_xboole_0 @ X0)
% 42.23/42.47          | ~ (r1_xboole_0 @ X0 @ X1)
% 42.23/42.47          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['75', '76'])).
% 42.23/42.47  thf('78', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 42.23/42.47      inference('sup-', [status(thm)], ['74', '77'])).
% 42.23/42.47  thf('79', plain,
% 42.23/42.47      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 42.23/42.47      inference('simplify', [status(thm)], ['78'])).
% 42.23/42.47  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 42.23/42.47      inference('sup-', [status(thm)], ['73', '79'])).
% 42.23/42.47  thf('81', plain,
% 42.23/42.47      (![X6 : $i, X7 : $i]:
% 42.23/42.47         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 42.23/42.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.23/42.47  thf('82', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 42.23/42.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 42.23/42.47  thf('83', plain,
% 42.23/42.47      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 42.23/42.47      inference('sup-', [status(thm)], ['81', '82'])).
% 42.23/42.47  thf('84', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 42.23/42.47      inference('sup-', [status(thm)], ['80', '83'])).
% 42.23/42.47  thf('85', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(cc5_funct_2, axiom,
% 42.23/42.47    (![A:$i,B:$i]:
% 42.23/42.47     ( ( ~( v1_xboole_0 @ B ) ) =>
% 42.23/42.47       ( ![C:$i]:
% 42.23/42.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.23/42.47           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 42.23/42.47             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 42.23/42.47  thf('86', plain,
% 42.23/42.47      (![X26 : $i, X27 : $i, X28 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 42.23/42.47          | (v1_partfun1 @ X26 @ X27)
% 42.23/42.47          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 42.23/42.47          | ~ (v1_funct_1 @ X26)
% 42.23/42.47          | (v1_xboole_0 @ X28))),
% 42.23/42.47      inference('cnf', [status(esa)], [cc5_funct_2])).
% 42.23/42.47  thf('87', plain,
% 42.23/42.47      (((v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | ~ (v1_funct_1 @ sk_E)
% 42.23/42.47        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 42.23/42.47        | (v1_partfun1 @ sk_E @ sk_C_1))),
% 42.23/42.47      inference('sup-', [status(thm)], ['85', '86'])).
% 42.23/42.47  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('89', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('90', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_E @ sk_C_1))),
% 42.23/42.47      inference('demod', [status(thm)], ['87', '88', '89'])).
% 42.23/42.47  thf('91', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('92', plain, ((v1_partfun1 @ sk_E @ sk_C_1)),
% 42.23/42.47      inference('clc', [status(thm)], ['90', '91'])).
% 42.23/42.47  thf(d4_partfun1, axiom,
% 42.23/42.47    (![A:$i,B:$i]:
% 42.23/42.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 42.23/42.47       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 42.23/42.47  thf('93', plain,
% 42.23/42.47      (![X29 : $i, X30 : $i]:
% 42.23/42.47         (~ (v1_partfun1 @ X30 @ X29)
% 42.23/42.47          | ((k1_relat_1 @ X30) = (X29))
% 42.23/42.47          | ~ (v4_relat_1 @ X30 @ X29)
% 42.23/42.47          | ~ (v1_relat_1 @ X30))),
% 42.23/42.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 42.23/42.47  thf('94', plain,
% 42.23/42.47      ((~ (v1_relat_1 @ sk_E)
% 42.23/42.47        | ~ (v4_relat_1 @ sk_E @ sk_C_1)
% 42.23/42.47        | ((k1_relat_1 @ sk_E) = (sk_C_1)))),
% 42.23/42.47      inference('sup-', [status(thm)], ['92', '93'])).
% 42.23/42.47  thf('95', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(cc1_relset_1, axiom,
% 42.23/42.47    (![A:$i,B:$i,C:$i]:
% 42.23/42.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.23/42.47       ( v1_relat_1 @ C ) ))).
% 42.23/42.47  thf('96', plain,
% 42.23/42.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 42.23/42.47         ((v1_relat_1 @ X20)
% 42.23/42.47          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 42.23/42.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.23/42.47  thf('97', plain, ((v1_relat_1 @ sk_E)),
% 42.23/42.47      inference('sup-', [status(thm)], ['95', '96'])).
% 42.23/42.47  thf('98', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf(cc2_relset_1, axiom,
% 42.23/42.47    (![A:$i,B:$i,C:$i]:
% 42.23/42.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 42.23/42.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 42.23/42.47  thf('99', plain,
% 42.23/42.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 42.23/42.47         ((v4_relat_1 @ X23 @ X24)
% 42.23/42.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 42.23/42.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 42.23/42.47  thf('100', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 42.23/42.47      inference('sup-', [status(thm)], ['98', '99'])).
% 42.23/42.47  thf('101', plain, (((k1_relat_1 @ sk_E) = (sk_C_1))),
% 42.23/42.47      inference('demod', [status(thm)], ['94', '97', '100'])).
% 42.23/42.47  thf(t187_relat_1, axiom,
% 42.23/42.47    (![A:$i]:
% 42.23/42.47     ( ( v1_relat_1 @ A ) =>
% 42.23/42.47       ( ![B:$i]:
% 42.23/42.47         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 42.23/42.47           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 42.23/42.47  thf('102', plain,
% 42.23/42.47      (![X16 : $i, X17 : $i]:
% 42.23/42.47         (~ (r1_xboole_0 @ X16 @ (k1_relat_1 @ X17))
% 42.23/42.47          | ((k7_relat_1 @ X17 @ X16) = (k1_xboole_0))
% 42.23/42.47          | ~ (v1_relat_1 @ X17))),
% 42.23/42.47      inference('cnf', [status(esa)], [t187_relat_1])).
% 42.23/42.47  thf('103', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 42.23/42.47          | ~ (v1_relat_1 @ sk_E)
% 42.23/42.47          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 42.23/42.47      inference('sup-', [status(thm)], ['101', '102'])).
% 42.23/42.47  thf('104', plain, ((v1_relat_1 @ sk_E)),
% 42.23/42.47      inference('sup-', [status(thm)], ['95', '96'])).
% 42.23/42.47  thf('105', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 42.23/42.47          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 42.23/42.47      inference('demod', [status(thm)], ['103', '104'])).
% 42.23/42.47  thf('106', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.47      inference('sup-', [status(thm)], ['84', '105'])).
% 42.23/42.47  thf('107', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 42.23/42.47      inference('sup-', [status(thm)], ['53', '54'])).
% 42.23/42.47  thf('108', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 42.23/42.47      inference('sup-', [status(thm)], ['62', '63'])).
% 42.23/42.47  thf('109', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('110', plain,
% 42.23/42.47      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 42.23/42.47          | ~ (v1_funct_1 @ X31)
% 42.23/42.47          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 42.23/42.47      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 42.23/42.47  thf('111', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 42.23/42.47          | ~ (v1_funct_1 @ sk_F))),
% 42.23/42.47      inference('sup-', [status(thm)], ['109', '110'])).
% 42.23/42.47  thf('112', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('113', plain,
% 42.23/42.47      (![X0 : $i]:
% 42.23/42.47         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 42.23/42.47      inference('demod', [status(thm)], ['111', '112'])).
% 42.23/42.47  thf('114', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 42.23/42.47      inference('sup-', [status(thm)], ['80', '83'])).
% 42.23/42.47  thf('115', plain,
% 42.23/42.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('116', plain,
% 42.23/42.47      (![X26 : $i, X27 : $i, X28 : $i]:
% 42.23/42.47         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 42.23/42.47          | (v1_partfun1 @ X26 @ X27)
% 42.23/42.47          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 42.23/42.47          | ~ (v1_funct_1 @ X26)
% 42.23/42.47          | (v1_xboole_0 @ X28))),
% 42.23/42.47      inference('cnf', [status(esa)], [cc5_funct_2])).
% 42.23/42.47  thf('117', plain,
% 42.23/42.47      (((v1_xboole_0 @ sk_B_1)
% 42.23/42.47        | ~ (v1_funct_1 @ sk_F)
% 42.23/42.47        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 42.23/42.47        | (v1_partfun1 @ sk_F @ sk_D))),
% 42.23/42.47      inference('sup-', [status(thm)], ['115', '116'])).
% 42.23/42.47  thf('118', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('119', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('120', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_F @ sk_D))),
% 42.23/42.47      inference('demod', [status(thm)], ['117', '118', '119'])).
% 42.23/42.47  thf('121', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 42.23/42.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.47  thf('122', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 42.23/42.47      inference('clc', [status(thm)], ['120', '121'])).
% 42.23/42.47  thf('123', plain,
% 42.23/42.47      (![X29 : $i, X30 : $i]:
% 42.23/42.47         (~ (v1_partfun1 @ X30 @ X29)
% 42.23/42.47          | ((k1_relat_1 @ X30) = (X29))
% 42.23/42.47          | ~ (v4_relat_1 @ X30 @ X29)
% 42.23/42.47          | ~ (v1_relat_1 @ X30))),
% 42.23/42.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 42.23/42.47  thf('124', plain,
% 42.23/42.47      ((~ (v1_relat_1 @ sk_F)
% 42.23/42.47        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 42.23/42.47        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 42.23/42.48      inference('sup-', [status(thm)], ['122', '123'])).
% 42.23/42.48  thf('125', plain,
% 42.23/42.48      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('126', plain,
% 42.23/42.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 42.23/42.48         ((v1_relat_1 @ X20)
% 42.23/42.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 42.23/42.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 42.23/42.48  thf('127', plain, ((v1_relat_1 @ sk_F)),
% 42.23/42.48      inference('sup-', [status(thm)], ['125', '126'])).
% 42.23/42.48  thf('128', plain,
% 42.23/42.48      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('129', plain,
% 42.23/42.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 42.23/42.48         ((v4_relat_1 @ X23 @ X24)
% 42.23/42.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 42.23/42.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 42.23/42.48  thf('130', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 42.23/42.48      inference('sup-', [status(thm)], ['128', '129'])).
% 42.23/42.48  thf('131', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 42.23/42.48      inference('demod', [status(thm)], ['124', '127', '130'])).
% 42.23/42.48  thf('132', plain,
% 42.23/42.48      (![X16 : $i, X17 : $i]:
% 42.23/42.48         (~ (r1_xboole_0 @ X16 @ (k1_relat_1 @ X17))
% 42.23/42.48          | ((k7_relat_1 @ X17 @ X16) = (k1_xboole_0))
% 42.23/42.48          | ~ (v1_relat_1 @ X17))),
% 42.23/42.48      inference('cnf', [status(esa)], [t187_relat_1])).
% 42.23/42.48  thf('133', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         (~ (r1_xboole_0 @ X0 @ sk_D)
% 42.23/42.48          | ~ (v1_relat_1 @ sk_F)
% 42.23/42.48          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 42.23/42.48      inference('sup-', [status(thm)], ['131', '132'])).
% 42.23/42.48  thf('134', plain, ((v1_relat_1 @ sk_F)),
% 42.23/42.48      inference('sup-', [status(thm)], ['125', '126'])).
% 42.23/42.48  thf('135', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         (~ (r1_xboole_0 @ X0 @ sk_D)
% 42.23/42.48          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 42.23/42.48      inference('demod', [status(thm)], ['133', '134'])).
% 42.23/42.48  thf('136', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['114', '135'])).
% 42.23/42.48  thf('137', plain,
% 42.23/42.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('138', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('139', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('140', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('141', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48            = (sk_E))
% 42.23/42.48        | ~ (v1_funct_2 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.48        | ~ (v1_funct_1 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ((k1_xboole_0) != (k1_xboole_0))
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A))),
% 42.23/42.48      inference('demod', [status(thm)],
% 42.23/42.48                ['48', '49', '50', '51', '52', '55', '64', '69', '106', '107', 
% 42.23/42.48                 '108', '113', '136', '137', '138', '139', '140'])).
% 42.23/42.48  thf('142', plain,
% 42.23/42.48      ((~ (v1_funct_1 @ 
% 42.23/42.48           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ~ (v1_funct_2 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48            = (sk_E))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify', [status(thm)], ['141'])).
% 42.23/42.48  thf('143', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48            = (sk_E))
% 42.23/42.48        | ~ (v1_funct_1 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 42.23/42.48      inference('sup-', [status(thm)], ['30', '142'])).
% 42.23/42.48  thf('144', plain,
% 42.23/42.48      ((~ (v1_funct_1 @ 
% 42.23/42.48           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48            = (sk_E))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify', [status(thm)], ['143'])).
% 42.23/42.48  thf('145', plain,
% 42.23/42.48      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48            != (sk_E))
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            != (sk_F)))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('146', plain,
% 42.23/42.48      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48          != (sk_E)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_C_1) = (sk_E))))),
% 42.23/42.48      inference('split', [status(esa)], ['145'])).
% 42.23/42.48  thf('147', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 42.23/42.48      inference('demod', [status(thm)], ['111', '112'])).
% 42.23/42.48  thf('148', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 42.23/42.48      inference('sup-', [status(thm)], ['53', '54'])).
% 42.23/42.48  thf('149', plain,
% 42.23/42.48      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 42.23/42.48      inference('split', [status(esa)], ['145'])).
% 42.23/42.48  thf('150', plain,
% 42.23/42.48      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 42.23/42.48      inference('sup-', [status(thm)], ['148', '149'])).
% 42.23/42.48  thf('151', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 42.23/42.48      inference('sup-', [status(thm)], ['53', '54'])).
% 42.23/42.48  thf('152', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['62', '63'])).
% 42.23/42.48  thf('153', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['62', '63'])).
% 42.23/42.48  thf('154', plain,
% 42.23/42.48      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0)
% 42.23/42.48          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 42.23/42.48      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 42.23/42.48  thf('155', plain,
% 42.23/42.48      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0)
% 42.23/42.48          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 42.23/42.48      inference('sup-', [status(thm)], ['147', '154'])).
% 42.23/42.48  thf('156', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 42.23/42.48           = (k7_relat_1 @ sk_E @ X0))),
% 42.23/42.48      inference('demod', [status(thm)], ['67', '68'])).
% 42.23/42.48  thf('157', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['84', '105'])).
% 42.23/42.48  thf('158', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['114', '135'])).
% 42.23/42.48  thf('159', plain,
% 42.23/42.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 42.23/42.48      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 42.23/42.48  thf('160', plain,
% 42.23/42.48      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 42.23/42.48      inference('simplify', [status(thm)], ['159'])).
% 42.23/42.48  thf('161', plain,
% 42.23/42.48      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('demod', [status(thm)], ['13', '14'])).
% 42.23/42.48  thf('162', plain,
% 42.23/42.48      (((v1_funct_2 @ 
% 42.23/42.48         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('demod', [status(thm)], ['28', '29'])).
% 42.23/42.48  thf('163', plain,
% 42.23/42.48      (((m1_subset_1 @ 
% 42.23/42.48         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48         (k1_zfmisc_1 @ 
% 42.23/42.48          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('demod', [status(thm)], ['43', '44'])).
% 42.23/42.48  thf('164', plain,
% 42.23/42.48      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 42.23/42.48         ((v1_xboole_0 @ X35)
% 42.23/42.48          | (v1_xboole_0 @ X36)
% 42.23/42.48          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 42.23/42.48          | ~ (v1_funct_1 @ X38)
% 42.23/42.48          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 42.23/42.48          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 42.23/42.48          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 42.23/42.48          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X36)
% 42.23/42.48              = (X38))
% 42.23/42.48          | ~ (m1_subset_1 @ X41 @ 
% 42.23/42.48               (k1_zfmisc_1 @ 
% 42.23/42.48                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 42.23/42.48          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 42.23/42.48          | ~ (v1_funct_1 @ X41)
% 42.23/42.48          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 42.23/42.48              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 42.23/42.48                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 42.23/42.48          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 42.23/42.48          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 42.23/42.48          | ~ (v1_funct_1 @ X39)
% 42.23/42.48          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 42.23/42.48          | (v1_xboole_0 @ X40)
% 42.23/42.48          | (v1_xboole_0 @ X37))),
% 42.23/42.48      inference('cnf', [status(esa)], [d1_tmap_1])).
% 42.23/42.48  thf('165', plain,
% 42.23/42.48      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 42.23/42.48         ((v1_xboole_0 @ X37)
% 42.23/42.48          | (v1_xboole_0 @ X40)
% 42.23/42.48          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 42.23/42.48          | ~ (v1_funct_1 @ X39)
% 42.23/42.48          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 42.23/42.48          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 42.23/42.48          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 42.23/42.48              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 42.23/42.48                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 42.23/42.48          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 42.23/42.48          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 42.23/42.48               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 42.23/42.48          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 42.23/42.48               (k1_zfmisc_1 @ 
% 42.23/42.48                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 42.23/42.48          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 42.23/42.48              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X36) = (
% 42.23/42.48              X38))
% 42.23/42.48          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 42.23/42.48          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 42.23/42.48          | ~ (v1_funct_1 @ X38)
% 42.23/42.48          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 42.23/42.48          | (v1_xboole_0 @ X36)
% 42.23/42.48          | (v1_xboole_0 @ X35))),
% 42.23/42.48      inference('simplify', [status(thm)], ['164'])).
% 42.23/42.48  thf('166', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.48        | ~ (v1_funct_1 @ sk_F)
% 42.23/42.48        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 42.23/42.48        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            = (sk_F))
% 42.23/42.48        | ~ (v1_funct_2 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.48        | ~ (v1_funct_1 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 42.23/42.48        | ~ (m1_subset_1 @ sk_E @ 
% 42.23/42.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 42.23/42.48        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 42.23/42.48        | ~ (v1_funct_1 @ sk_E)
% 42.23/42.48        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A))),
% 42.23/42.48      inference('sup-', [status(thm)], ['163', '165'])).
% 42.23/42.48  thf('167', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('168', plain, ((v1_funct_1 @ sk_F)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('169', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('170', plain,
% 42.23/42.48      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('171', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 42.23/42.48      inference('sup-', [status(thm)], ['53', '54'])).
% 42.23/42.48  thf('172', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['62', '63'])).
% 42.23/42.48  thf('173', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 42.23/42.48           = (k7_relat_1 @ sk_E @ X0))),
% 42.23/42.48      inference('demod', [status(thm)], ['67', '68'])).
% 42.23/42.48  thf('174', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['84', '105'])).
% 42.23/42.48  thf('175', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 42.23/42.48      inference('sup-', [status(thm)], ['53', '54'])).
% 42.23/42.48  thf('176', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['62', '63'])).
% 42.23/42.48  thf('177', plain,
% 42.23/42.48      (![X0 : $i]:
% 42.23/42.48         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 42.23/42.48      inference('demod', [status(thm)], ['111', '112'])).
% 42.23/42.48  thf('178', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 42.23/42.48      inference('sup-', [status(thm)], ['114', '135'])).
% 42.23/42.48  thf('179', plain,
% 42.23/42.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('180', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('181', plain, ((v1_funct_1 @ sk_E)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('182', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('183', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            = (sk_F))
% 42.23/42.48        | ~ (v1_funct_2 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.48        | ~ (v1_funct_1 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ((k1_xboole_0) != (k1_xboole_0))
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A))),
% 42.23/42.48      inference('demod', [status(thm)],
% 42.23/42.48                ['166', '167', '168', '169', '170', '171', '172', '173', 
% 42.23/42.48                 '174', '175', '176', '177', '178', '179', '180', '181', '182'])).
% 42.23/42.48  thf('184', plain,
% 42.23/42.48      ((~ (v1_funct_1 @ 
% 42.23/42.48           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ~ (v1_funct_2 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            = (sk_F))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify', [status(thm)], ['183'])).
% 42.23/42.48  thf('185', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            = (sk_F))
% 42.23/42.48        | ~ (v1_funct_1 @ 
% 42.23/42.48             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 42.23/42.48      inference('sup-', [status(thm)], ['162', '184'])).
% 42.23/42.48  thf('186', plain,
% 42.23/42.48      ((~ (v1_funct_1 @ 
% 42.23/42.48           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            = (sk_F))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify', [status(thm)], ['185'])).
% 42.23/42.48  thf('187', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48            = (sk_F)))),
% 42.23/42.48      inference('sup-', [status(thm)], ['161', '186'])).
% 42.23/42.48  thf('188', plain,
% 42.23/42.48      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48          = (sk_F))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify', [status(thm)], ['187'])).
% 42.23/42.48  thf('189', plain,
% 42.23/42.48      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48          != (sk_F)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_D) = (sk_F))))),
% 42.23/42.48      inference('split', [status(esa)], ['145'])).
% 42.23/42.48  thf('190', plain,
% 42.23/42.48      (((((sk_F) != (sk_F))
% 42.23/42.48         | (v1_xboole_0 @ sk_D)
% 42.23/42.48         | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48         | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48         | (v1_xboole_0 @ sk_A)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_D) = (sk_F))))),
% 42.23/42.48      inference('sup-', [status(thm)], ['188', '189'])).
% 42.23/42.48  thf('191', plain,
% 42.23/42.48      ((((v1_xboole_0 @ sk_A)
% 42.23/42.48         | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48         | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48         | (v1_xboole_0 @ sk_D)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_D) = (sk_F))))),
% 42.23/42.48      inference('simplify', [status(thm)], ['190'])).
% 42.23/42.48  thf('192', plain, (~ (v1_xboole_0 @ sk_D)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('193', plain,
% 42.23/42.48      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_D) = (sk_F))))),
% 42.23/42.48      inference('sup-', [status(thm)], ['191', '192'])).
% 42.23/42.48  thf('194', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('195', plain,
% 42.23/42.48      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_D) = (sk_F))))),
% 42.23/42.48      inference('clc', [status(thm)], ['193', '194'])).
% 42.23/42.48  thf('196', plain, (~ (v1_xboole_0 @ sk_A)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('197', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_B_1))
% 42.23/42.48         <= (~
% 42.23/42.48             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 42.23/42.48                sk_D) = (sk_F))))),
% 42.23/42.48      inference('clc', [status(thm)], ['195', '196'])).
% 42.23/42.48  thf('198', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('199', plain,
% 42.23/42.48      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48          = (sk_F)))),
% 42.23/42.48      inference('sup-', [status(thm)], ['197', '198'])).
% 42.23/42.48  thf('200', plain,
% 42.23/42.48      (~
% 42.23/42.48       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48          = (sk_E))) | 
% 42.23/42.48       ~
% 42.23/42.48       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 42.23/42.48          = (sk_F))) | 
% 42.23/42.48       ~
% 42.23/42.48       (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 42.23/42.48          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 42.23/42.48          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 42.23/42.48             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 42.23/42.48      inference('split', [status(esa)], ['145'])).
% 42.23/42.48  thf('201', plain,
% 42.23/42.48      (~
% 42.23/42.48       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48          = (sk_E)))),
% 42.23/42.48      inference('sat_resolution*', [status(thm)], ['160', '199', '200'])).
% 42.23/42.48  thf('202', plain,
% 42.23/42.48      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 42.23/42.48         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 42.23/42.48         != (sk_E))),
% 42.23/42.48      inference('simpl_trail', [status(thm)], ['146', '201'])).
% 42.23/42.48  thf('203', plain,
% 42.23/42.48      ((~ (v1_funct_1 @ 
% 42.23/42.48           (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify_reflect-', [status(thm)], ['144', '202'])).
% 42.23/42.48  thf('204', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_D)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_A))),
% 42.23/42.48      inference('sup-', [status(thm)], ['15', '203'])).
% 42.23/42.48  thf('205', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_A)
% 42.23/42.48        | (v1_xboole_0 @ sk_B_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_C_1)
% 42.23/42.48        | (v1_xboole_0 @ sk_D))),
% 42.23/42.48      inference('simplify', [status(thm)], ['204'])).
% 42.23/42.48  thf('206', plain, (~ (v1_xboole_0 @ sk_D)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('207', plain,
% 42.23/42.48      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 42.23/42.48      inference('sup-', [status(thm)], ['205', '206'])).
% 42.23/42.48  thf('208', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('209', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 42.23/42.48      inference('clc', [status(thm)], ['207', '208'])).
% 42.23/42.48  thf('210', plain, (~ (v1_xboole_0 @ sk_A)),
% 42.23/42.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.23/42.48  thf('211', plain, ((v1_xboole_0 @ sk_B_1)),
% 42.23/42.48      inference('clc', [status(thm)], ['209', '210'])).
% 42.23/42.48  thf('212', plain, ($false), inference('demod', [status(thm)], ['0', '211'])).
% 42.23/42.48  
% 42.23/42.48  % SZS output end Refutation
% 42.23/42.48  
% 42.23/42.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
