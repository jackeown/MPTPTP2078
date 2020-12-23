%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CVdIY33zHf

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:55 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  329 (2326 expanded)
%              Number of leaves         :   45 ( 784 expanded)
%              Depth                    :   40
%              Number of atoms          : 4202 (52900 expanded)
%              Number of equality atoms :  174 (1883 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
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
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
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
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49 ) @ ( k4_subset_1 @ X48 @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
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
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ),
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
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X48 @ X45 @ X47 ) @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
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
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ) ) ),
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
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( X43
       != ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ X43 @ X42 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ X42 )
        = X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_subset_1 @ X18 @ X19 ) ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
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
      ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf(rc1_yellow_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_yellow_1 @ B )
      & ( v1_partfun1 @ B @ A )
      & ( v1_funct_1 @ B )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('71',plain,(
    ! [X35: $i] :
      ( v1_partfun1 @ ( sk_B @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('72',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v4_relat_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( k1_relat_1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('75',plain,(
    ! [X35: $i] :
      ( v4_relat_1 @ ( sk_B @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ X14 @ X15 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( sk_B @ X0 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ ( sk_B @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('93',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    r1_xboole_0 @ sk_C @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X35: $i] :
      ( v1_partfun1 @ ( sk_B @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(t134_pboole,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('96',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_partfun1 @ X36 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v4_relat_1 @ X36 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t134_pboole])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v4_relat_1 @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('99',plain,(
    ! [X35: $i] :
      ( v4_relat_1 @ ( sk_B @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('100',plain,(
    ! [X35: $i] :
      ( v1_funct_1 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('101',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X35: $i] :
      ( v1_partfun1 @ ( sk_B @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('103',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('106',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('107',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('110',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','108','111'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('113',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k7_relat_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','116'])).

thf('118',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('119',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_C ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','108','111'])).

thf('121',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','108','111'])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('123',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_C ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
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

thf('128',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('129',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('139',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('142',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['136','139','142'])).

thf('144',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k7_relat_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['137','138'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('150',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('151',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('158',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k7_relat_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( ( k7_relat_1 @ ( sk_B @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k7_relat_1 @ ( sk_B @ sk_D ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['156','161'])).

thf('163',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('164',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ ( sk_B @ sk_D ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','108','111'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('167',plain,(
    ! [X35: $i] :
      ( v1_relat_1 @ ( sk_B @ X35 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('168',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('170',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_D @ ( k3_xboole_0 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('172',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_D @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    r1_xboole_0 @ sk_D @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('175',plain,
    ( ( k7_relat_1 @ k1_xboole_0 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('177',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_D ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','108','111'])).

thf('179',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','108','111'])).

thf('180',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('181',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('183',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_D ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('197',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('200',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['194','197','200'])).

thf('202',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k7_relat_1 @ X13 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['195','196'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['184','205'])).

thf('207',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','148','149','150','155','206','207','208','209','210'])).

thf('212',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('217',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['213'])).

thf('218',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('220',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['215','220'])).

thf('222',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('224',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','147'])).

thf('225',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('226',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['184','205'])).

thf('227',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['221','222','223','224','225','226'])).

thf('228',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('230',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('231',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('232',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( X43
       != ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ X43 @ X38 )
        = X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('233',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ X38 )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['231','233'])).

thf('235',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('240',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('242',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['126','147'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('244',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('246',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['184','205'])).

thf('247',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['234','235','236','237','238','239','240','241','242','243','244','245','246','247','248','249','250'])).

thf('252',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['230','252'])).

thf('254',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['229','254'])).

thf('256',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['213'])).

thf('258',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['213'])).

thf('269',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['228','267','268'])).

thf('270',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['214','269'])).

thf('271',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['212','270'])).

thf('272',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','271'])).

thf('273',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','273'])).

thf('275',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['277','278'])).

thf('280',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    $false ),
    inference(demod,[status(thm)],['0','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CVdIY33zHf
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.21/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.21/1.41  % Solved by: fo/fo7.sh
% 1.21/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.41  % done 1466 iterations in 0.950s
% 1.21/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.21/1.41  % SZS output start Refutation
% 1.21/1.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.21/1.41  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.21/1.41  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.21/1.41  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.21/1.41  thf(sk_F_type, type, sk_F: $i).
% 1.21/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.21/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.21/1.41  thf(sk_E_type, type, sk_E: $i).
% 1.21/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.21/1.41  thf(sk_D_type, type, sk_D: $i).
% 1.21/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.41  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.21/1.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.21/1.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.21/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.41  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 1.21/1.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.21/1.41  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 1.21/1.41  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 1.21/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.21/1.41  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.21/1.41  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.21/1.41  thf(sk_B_type, type, sk_B: $i > $i).
% 1.21/1.41  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.21/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.21/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.41  thf(t6_tmap_1, conjecture,
% 1.21/1.41    (![A:$i]:
% 1.21/1.41     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.21/1.41       ( ![B:$i]:
% 1.21/1.41         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.41           ( ![C:$i]:
% 1.21/1.41             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.21/1.41                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.41               ( ![D:$i]:
% 1.21/1.41                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.21/1.41                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.41                   ( ( r1_subset_1 @ C @ D ) =>
% 1.21/1.41                     ( ![E:$i]:
% 1.21/1.41                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.21/1.41                           ( m1_subset_1 @
% 1.21/1.41                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.21/1.41                         ( ![F:$i]:
% 1.21/1.41                           ( ( ( v1_funct_1 @ F ) & 
% 1.21/1.41                               ( v1_funct_2 @ F @ D @ B ) & 
% 1.21/1.41                               ( m1_subset_1 @
% 1.21/1.41                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.21/1.41                             ( ( ( k2_partfun1 @
% 1.21/1.41                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.21/1.41                                 ( k2_partfun1 @
% 1.21/1.41                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.21/1.41                               ( ( k2_partfun1 @
% 1.21/1.41                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.21/1.41                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.21/1.41                                 ( E ) ) & 
% 1.21/1.41                               ( ( k2_partfun1 @
% 1.21/1.41                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.21/1.41                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.21/1.41                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.21/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.41    (~( ![A:$i]:
% 1.21/1.41        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.21/1.41          ( ![B:$i]:
% 1.21/1.41            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.41              ( ![C:$i]:
% 1.21/1.41                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.21/1.41                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.41                  ( ![D:$i]:
% 1.21/1.41                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.21/1.41                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.41                      ( ( r1_subset_1 @ C @ D ) =>
% 1.21/1.41                        ( ![E:$i]:
% 1.21/1.41                          ( ( ( v1_funct_1 @ E ) & 
% 1.21/1.41                              ( v1_funct_2 @ E @ C @ B ) & 
% 1.21/1.41                              ( m1_subset_1 @
% 1.21/1.41                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.21/1.41                            ( ![F:$i]:
% 1.21/1.41                              ( ( ( v1_funct_1 @ F ) & 
% 1.21/1.41                                  ( v1_funct_2 @ F @ D @ B ) & 
% 1.21/1.41                                  ( m1_subset_1 @
% 1.21/1.41                                    F @ 
% 1.21/1.41                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.21/1.41                                ( ( ( k2_partfun1 @
% 1.21/1.41                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.21/1.41                                    ( k2_partfun1 @
% 1.21/1.41                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.21/1.41                                  ( ( k2_partfun1 @
% 1.21/1.41                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.21/1.41                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.21/1.41                                    ( E ) ) & 
% 1.21/1.41                                  ( ( k2_partfun1 @
% 1.21/1.41                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.21/1.41                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.21/1.41                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.21/1.41    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 1.21/1.41  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('2', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('3', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(dt_k1_tmap_1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.21/1.41     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.21/1.41         ( ~( v1_xboole_0 @ C ) ) & 
% 1.21/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 1.21/1.41         ( ~( v1_xboole_0 @ D ) ) & 
% 1.21/1.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 1.21/1.41         ( v1_funct_2 @ E @ C @ B ) & 
% 1.21/1.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.21/1.41         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.21/1.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.21/1.41       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.21/1.41         ( v1_funct_2 @
% 1.21/1.41           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.21/1.41           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.21/1.41         ( m1_subset_1 @
% 1.21/1.41           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.21/1.41           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 1.21/1.41  thf('4', plain,
% 1.21/1.41      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.21/1.41          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.21/1.41          | ~ (v1_funct_1 @ X44)
% 1.21/1.41          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 1.21/1.41          | (v1_xboole_0 @ X47)
% 1.21/1.41          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X48))
% 1.21/1.41          | (v1_xboole_0 @ X45)
% 1.21/1.41          | (v1_xboole_0 @ X46)
% 1.21/1.41          | (v1_xboole_0 @ X48)
% 1.21/1.41          | ~ (v1_funct_1 @ X49)
% 1.21/1.41          | ~ (v1_funct_2 @ X49 @ X47 @ X46)
% 1.21/1.41          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 1.21/1.41          | (v1_funct_1 @ (k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49)))),
% 1.21/1.41      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.21/1.41  thf('5', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.41         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.21/1.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.21/1.41          | ~ (v1_funct_1 @ X0)
% 1.21/1.41          | (v1_xboole_0 @ X2)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 1.21/1.41          | (v1_xboole_0 @ X1)
% 1.21/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.21/1.41          | ~ (v1_funct_1 @ sk_E)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 1.21/1.41      inference('sup-', [status(thm)], ['3', '4'])).
% 1.21/1.41  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('8', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.41         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.21/1.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.21/1.41          | ~ (v1_funct_1 @ X0)
% 1.21/1.41          | (v1_xboole_0 @ X2)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 1.21/1.41          | (v1_xboole_0 @ X1)
% 1.21/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.21/1.41      inference('demod', [status(thm)], ['5', '6', '7'])).
% 1.21/1.41  thf('9', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_D)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (v1_funct_1 @ sk_F)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.21/1.41          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['2', '8'])).
% 1.21/1.41  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('12', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_D)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.21/1.41      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.21/1.41  thf('13', plain,
% 1.21/1.41      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['1', '12'])).
% 1.21/1.41  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('15', plain,
% 1.21/1.41      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['13', '14'])).
% 1.21/1.41  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('17', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('18', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('19', plain,
% 1.21/1.41      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.21/1.41          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.21/1.41          | ~ (v1_funct_1 @ X44)
% 1.21/1.41          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 1.21/1.41          | (v1_xboole_0 @ X47)
% 1.21/1.41          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X48))
% 1.21/1.41          | (v1_xboole_0 @ X45)
% 1.21/1.41          | (v1_xboole_0 @ X46)
% 1.21/1.41          | (v1_xboole_0 @ X48)
% 1.21/1.41          | ~ (v1_funct_1 @ X49)
% 1.21/1.41          | ~ (v1_funct_2 @ X49 @ X47 @ X46)
% 1.21/1.41          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 1.21/1.41          | (v1_funct_2 @ (k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49) @ 
% 1.21/1.41             (k4_subset_1 @ X48 @ X45 @ X47) @ X46))),
% 1.21/1.41      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.21/1.41  thf('20', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.41         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.21/1.41           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 1.21/1.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.21/1.41          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.21/1.41          | ~ (v1_funct_1 @ X2)
% 1.21/1.41          | (v1_xboole_0 @ X1)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.21/1.41          | ~ (v1_funct_1 @ sk_E)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 1.21/1.41      inference('sup-', [status(thm)], ['18', '19'])).
% 1.21/1.41  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('23', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.41         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.21/1.41           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 1.21/1.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.21/1.41          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.21/1.41          | ~ (v1_funct_1 @ X2)
% 1.21/1.41          | (v1_xboole_0 @ X1)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.21/1.41  thf('24', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_D)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (v1_funct_1 @ sk_F)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.21/1.41          | (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 1.21/1.41      inference('sup-', [status(thm)], ['17', '23'])).
% 1.21/1.41  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('27', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_D)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 1.21/1.41      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.21/1.41  thf('28', plain,
% 1.21/1.41      (((v1_funct_2 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['16', '27'])).
% 1.21/1.41  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('30', plain,
% 1.21/1.41      (((v1_funct_2 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.41  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('32', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('33', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('34', plain,
% 1.21/1.41      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.21/1.41          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.21/1.41          | ~ (v1_funct_1 @ X44)
% 1.21/1.41          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 1.21/1.41          | (v1_xboole_0 @ X47)
% 1.21/1.41          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X48))
% 1.21/1.41          | (v1_xboole_0 @ X45)
% 1.21/1.41          | (v1_xboole_0 @ X46)
% 1.21/1.41          | (v1_xboole_0 @ X48)
% 1.21/1.41          | ~ (v1_funct_1 @ X49)
% 1.21/1.41          | ~ (v1_funct_2 @ X49 @ X47 @ X46)
% 1.21/1.41          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 1.21/1.41          | (m1_subset_1 @ (k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49) @ 
% 1.21/1.41             (k1_zfmisc_1 @ 
% 1.21/1.41              (k2_zfmisc_1 @ (k4_subset_1 @ X48 @ X45 @ X47) @ X46))))),
% 1.21/1.41      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.21/1.41  thf('35', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.41         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.21/1.41           (k1_zfmisc_1 @ 
% 1.21/1.41            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 1.21/1.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.21/1.41          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.21/1.41          | ~ (v1_funct_1 @ X2)
% 1.21/1.41          | (v1_xboole_0 @ X1)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.21/1.41          | ~ (v1_funct_1 @ sk_E)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 1.21/1.41      inference('sup-', [status(thm)], ['33', '34'])).
% 1.21/1.41  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('38', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.41         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.21/1.41           (k1_zfmisc_1 @ 
% 1.21/1.41            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 1.21/1.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.21/1.41          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.21/1.41          | ~ (v1_funct_1 @ X2)
% 1.21/1.41          | (v1_xboole_0 @ X1)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.21/1.41  thf('39', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_D)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | ~ (v1_funct_1 @ sk_F)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.21/1.41          | (m1_subset_1 @ 
% 1.21/1.41             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k1_zfmisc_1 @ 
% 1.21/1.41              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['32', '38'])).
% 1.21/1.41  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('42', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_D)
% 1.21/1.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.21/1.41          | (v1_xboole_0 @ sk_C)
% 1.21/1.41          | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41          | (v1_xboole_0 @ X0)
% 1.21/1.41          | (m1_subset_1 @ 
% 1.21/1.41             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k1_zfmisc_1 @ 
% 1.21/1.41              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 1.21/1.41      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.21/1.41  thf('43', plain,
% 1.21/1.41      (((m1_subset_1 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41         (k1_zfmisc_1 @ 
% 1.21/1.41          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['31', '42'])).
% 1.21/1.41  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('45', plain,
% 1.21/1.41      (((m1_subset_1 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41         (k1_zfmisc_1 @ 
% 1.21/1.41          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['43', '44'])).
% 1.21/1.41  thf(d1_tmap_1, axiom,
% 1.21/1.41    (![A:$i]:
% 1.21/1.41     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.21/1.41       ( ![B:$i]:
% 1.21/1.41         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.41           ( ![C:$i]:
% 1.21/1.41             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.21/1.41                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.41               ( ![D:$i]:
% 1.21/1.41                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.21/1.41                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.21/1.41                   ( ![E:$i]:
% 1.21/1.41                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.21/1.41                         ( m1_subset_1 @
% 1.21/1.41                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.21/1.41                       ( ![F:$i]:
% 1.21/1.41                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.21/1.41                             ( m1_subset_1 @
% 1.21/1.41                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.21/1.41                           ( ( ( k2_partfun1 @
% 1.21/1.41                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.21/1.41                               ( k2_partfun1 @
% 1.21/1.41                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 1.21/1.41                             ( ![G:$i]:
% 1.21/1.41                               ( ( ( v1_funct_1 @ G ) & 
% 1.21/1.41                                   ( v1_funct_2 @
% 1.21/1.41                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.21/1.41                                   ( m1_subset_1 @
% 1.21/1.41                                     G @ 
% 1.21/1.41                                     ( k1_zfmisc_1 @
% 1.21/1.41                                       ( k2_zfmisc_1 @
% 1.21/1.41                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 1.21/1.41                                 ( ( ( G ) =
% 1.21/1.41                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.21/1.41                                   ( ( ( k2_partfun1 @
% 1.21/1.41                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.21/1.41                                         C ) =
% 1.21/1.41                                       ( E ) ) & 
% 1.21/1.41                                     ( ( k2_partfun1 @
% 1.21/1.41                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.21/1.41                                         D ) =
% 1.21/1.41                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.21/1.41  thf('46', plain,
% 1.21/1.41      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.21/1.41         ((v1_xboole_0 @ X37)
% 1.21/1.41          | (v1_xboole_0 @ X38)
% 1.21/1.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | ~ (v1_funct_1 @ X40)
% 1.21/1.41          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 1.21/1.41          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.21/1.41          | ((X43) != (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 1.21/1.41          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ X43 @ X42)
% 1.21/1.41              = (X41))
% 1.21/1.41          | ~ (m1_subset_1 @ X43 @ 
% 1.21/1.41               (k1_zfmisc_1 @ 
% 1.21/1.41                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 1.21/1.41          | ~ (v1_funct_2 @ X43 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 1.21/1.41          | ~ (v1_funct_1 @ X43)
% 1.21/1.41          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 1.21/1.41              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 1.21/1.41                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 1.21/1.41          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 1.21/1.41          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 1.21/1.41          | ~ (v1_funct_1 @ X41)
% 1.21/1.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | (v1_xboole_0 @ X42)
% 1.21/1.41          | (v1_xboole_0 @ X39))),
% 1.21/1.41      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.21/1.41  thf('47', plain,
% 1.21/1.41      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.21/1.41         ((v1_xboole_0 @ X39)
% 1.21/1.41          | (v1_xboole_0 @ X42)
% 1.21/1.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | ~ (v1_funct_1 @ X41)
% 1.21/1.41          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 1.21/1.41          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 1.21/1.41          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 1.21/1.41              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 1.21/1.41                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 1.21/1.41          | ~ (v1_funct_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 1.21/1.41          | ~ (v1_funct_2 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 1.21/1.41               (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 1.21/1.41          | ~ (m1_subset_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 1.21/1.41               (k1_zfmisc_1 @ 
% 1.21/1.41                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 1.21/1.41          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ 
% 1.21/1.41              (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ X42) = (
% 1.21/1.41              X41))
% 1.21/1.41          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.21/1.41          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 1.21/1.41          | ~ (v1_funct_1 @ X40)
% 1.21/1.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | (v1_xboole_0 @ X38)
% 1.21/1.41          | (v1_xboole_0 @ X37))),
% 1.21/1.41      inference('simplify', [status(thm)], ['46'])).
% 1.21/1.41  thf('48', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | ~ (v1_funct_1 @ sk_F)
% 1.21/1.41        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41            = (sk_E))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.21/1.41        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 1.21/1.41        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ sk_E)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_A))),
% 1.21/1.41      inference('sup-', [status(thm)], ['45', '47'])).
% 1.21/1.41  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('52', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(redefinition_k9_subset_1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.21/1.41       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.21/1.41  thf('54', plain,
% 1.21/1.41      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.21/1.41         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 1.21/1.41          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 1.21/1.41      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.21/1.41  thf('55', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.21/1.41  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(redefinition_r1_subset_1, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.21/1.41       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 1.21/1.41  thf('57', plain,
% 1.21/1.41      (![X18 : $i, X19 : $i]:
% 1.21/1.41         ((v1_xboole_0 @ X18)
% 1.21/1.41          | (v1_xboole_0 @ X19)
% 1.21/1.41          | (r1_xboole_0 @ X18 @ X19)
% 1.21/1.41          | ~ (r1_subset_1 @ X18 @ X19))),
% 1.21/1.41      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 1.21/1.41  thf('58', plain,
% 1.21/1.41      (((r1_xboole_0 @ sk_C @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C))),
% 1.21/1.41      inference('sup-', [status(thm)], ['56', '57'])).
% 1.21/1.41  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 1.21/1.41      inference('clc', [status(thm)], ['58', '59'])).
% 1.21/1.41  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.21/1.41      inference('clc', [status(thm)], ['60', '61'])).
% 1.21/1.41  thf(d7_xboole_0, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.21/1.41       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.21/1.41  thf('63', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.21/1.41      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.21/1.41  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('65', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(redefinition_k2_partfun1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i,D:$i]:
% 1.21/1.41     ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.21/1.41       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.21/1.41  thf('66', plain,
% 1.21/1.41      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.21/1.41          | ~ (v1_funct_1 @ X31)
% 1.21/1.41          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 1.21/1.41      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.21/1.41  thf('67', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 1.21/1.41          | ~ (v1_funct_1 @ sk_E))),
% 1.21/1.41      inference('sup-', [status(thm)], ['65', '66'])).
% 1.21/1.41  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('69', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['67', '68'])).
% 1.21/1.41  thf('70', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf(rc1_yellow_1, axiom,
% 1.21/1.41    (![A:$i]:
% 1.21/1.41     ( ?[B:$i]:
% 1.21/1.41       ( ( v1_yellow_1 @ B ) & ( v1_partfun1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 1.21/1.41         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) ) ))).
% 1.21/1.41  thf('71', plain, (![X35 : $i]: (v1_partfun1 @ (sk_B @ X35) @ X35)),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf(d4_partfun1, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.21/1.41       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.21/1.41  thf('72', plain,
% 1.21/1.41      (![X29 : $i, X30 : $i]:
% 1.21/1.41         (~ (v1_partfun1 @ X30 @ X29)
% 1.21/1.41          | ((k1_relat_1 @ X30) = (X29))
% 1.21/1.41          | ~ (v4_relat_1 @ X30 @ X29)
% 1.21/1.41          | ~ (v1_relat_1 @ X30))),
% 1.21/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.21/1.41  thf('73', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_relat_1 @ (sk_B @ X0))
% 1.21/1.41          | ~ (v4_relat_1 @ (sk_B @ X0) @ X0)
% 1.21/1.41          | ((k1_relat_1 @ (sk_B @ X0)) = (X0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['71', '72'])).
% 1.21/1.41  thf('74', plain, (![X35 : $i]: (v1_relat_1 @ (sk_B @ X35))),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('75', plain, (![X35 : $i]: (v4_relat_1 @ (sk_B @ X35) @ X35)),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('76', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B @ X0)) = (X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.21/1.41  thf(t90_relat_1, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( v1_relat_1 @ B ) =>
% 1.21/1.41       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.21/1.41         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.21/1.41  thf('77', plain,
% 1.21/1.41      (![X16 : $i, X17 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 1.21/1.41            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 1.21/1.41          | ~ (v1_relat_1 @ X16))),
% 1.21/1.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.21/1.41  thf(t192_relat_1, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( v1_relat_1 @ B ) =>
% 1.21/1.41       ( ( k7_relat_1 @ B @ A ) =
% 1.21/1.41         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 1.21/1.41  thf('78', plain,
% 1.21/1.41      (![X14 : $i, X15 : $i]:
% 1.21/1.41         (((k7_relat_1 @ X14 @ X15)
% 1.21/1.41            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15)))
% 1.21/1.41          | ~ (v1_relat_1 @ X14))),
% 1.21/1.41      inference('cnf', [status(esa)], [t192_relat_1])).
% 1.21/1.41  thf('79', plain,
% 1.21/1.41      (![X16 : $i, X17 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 1.21/1.41            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 1.21/1.41          | ~ (v1_relat_1 @ X16))),
% 1.21/1.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.21/1.41  thf('80', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.21/1.41            = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.21/1.41               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 1.21/1.41          | ~ (v1_relat_1 @ X1)
% 1.21/1.41          | ~ (v1_relat_1 @ X1))),
% 1.21/1.41      inference('sup+', [status(thm)], ['78', '79'])).
% 1.21/1.41  thf('81', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (~ (v1_relat_1 @ X1)
% 1.21/1.41          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.21/1.41              = (k3_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.21/1.41                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 1.21/1.41      inference('simplify', [status(thm)], ['80'])).
% 1.21/1.41  thf('82', plain,
% 1.21/1.41      (![X0 : $i, X2 : $i]:
% 1.21/1.41         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.21/1.41      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.21/1.41  thf('83', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) != (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ X1)
% 1.21/1.41          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.21/1.41             (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['81', '82'])).
% 1.21/1.41  thf('84', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ X1)
% 1.21/1.41          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.21/1.41             (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.21/1.41          | ~ (v1_relat_1 @ X1))),
% 1.21/1.41      inference('sup-', [status(thm)], ['77', '83'])).
% 1.21/1.41  thf('85', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ 
% 1.21/1.41           (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.21/1.41          | ~ (v1_relat_1 @ X1)
% 1.21/1.41          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0)))),
% 1.21/1.41      inference('simplify', [status(thm)], ['84'])).
% 1.21/1.41  thf('86', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k3_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ (sk_B @ X0))
% 1.21/1.41          | (r1_xboole_0 @ (k1_relat_1 @ (sk_B @ X0)) @ 
% 1.21/1.41             (k3_xboole_0 @ (k1_relat_1 @ (sk_B @ X0)) @ X1)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['76', '85'])).
% 1.21/1.41  thf('87', plain, (![X35 : $i]: (v1_relat_1 @ (sk_B @ X35))),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('88', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B @ X0)) = (X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.21/1.41  thf('89', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B @ X0)) = (X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.21/1.41  thf('90', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k3_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 1.21/1.41          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.21/1.41  thf('91', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.41        | (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_D)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['70', '90'])).
% 1.21/1.41  thf('92', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('93', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_C @ k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['91', '92'])).
% 1.21/1.41  thf('94', plain, ((r1_xboole_0 @ sk_C @ k1_xboole_0)),
% 1.21/1.41      inference('simplify', [status(thm)], ['93'])).
% 1.21/1.41  thf('95', plain, (![X35 : $i]: (v1_partfun1 @ (sk_B @ X35) @ X35)),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf(t134_pboole, axiom,
% 1.21/1.41    (![A:$i]:
% 1.21/1.41     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 1.21/1.41         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) ) =>
% 1.21/1.41       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.21/1.41  thf('96', plain,
% 1.21/1.41      (![X36 : $i]:
% 1.21/1.41         (((X36) = (k1_xboole_0))
% 1.21/1.41          | ~ (v1_partfun1 @ X36 @ k1_xboole_0)
% 1.21/1.41          | ~ (v1_funct_1 @ X36)
% 1.21/1.41          | ~ (v4_relat_1 @ X36 @ k1_xboole_0)
% 1.21/1.41          | ~ (v1_relat_1 @ X36))),
% 1.21/1.41      inference('cnf', [status(esa)], [t134_pboole])).
% 1.21/1.41  thf('97', plain,
% 1.21/1.41      ((~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 1.21/1.41        | ~ (v4_relat_1 @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 1.21/1.41        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 1.21/1.41        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['95', '96'])).
% 1.21/1.41  thf('98', plain, (![X35 : $i]: (v1_relat_1 @ (sk_B @ X35))),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('99', plain, (![X35 : $i]: (v4_relat_1 @ (sk_B @ X35) @ X35)),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('100', plain, (![X35 : $i]: (v1_funct_1 @ (sk_B @ X35))),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('101', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 1.21/1.41  thf('102', plain, (![X35 : $i]: (v1_partfun1 @ (sk_B @ X35) @ X35)),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('103', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.21/1.41      inference('sup+', [status(thm)], ['101', '102'])).
% 1.21/1.41  thf('104', plain,
% 1.21/1.41      (![X29 : $i, X30 : $i]:
% 1.21/1.41         (~ (v1_partfun1 @ X30 @ X29)
% 1.21/1.41          | ((k1_relat_1 @ X30) = (X29))
% 1.21/1.41          | ~ (v4_relat_1 @ X30 @ X29)
% 1.21/1.41          | ~ (v1_relat_1 @ X30))),
% 1.21/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.21/1.41  thf('105', plain,
% 1.21/1.41      ((~ (v1_relat_1 @ k1_xboole_0)
% 1.21/1.41        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.21/1.41        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['103', '104'])).
% 1.21/1.41  thf(t4_subset_1, axiom,
% 1.21/1.41    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.21/1.41  thf('106', plain,
% 1.21/1.41      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.21/1.41      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.21/1.41  thf(cc1_relset_1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.41       ( v1_relat_1 @ C ) ))).
% 1.21/1.41  thf('107', plain,
% 1.21/1.41      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.21/1.41         ((v1_relat_1 @ X20)
% 1.21/1.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.21/1.41  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.21/1.41      inference('sup-', [status(thm)], ['106', '107'])).
% 1.21/1.41  thf('109', plain,
% 1.21/1.41      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.21/1.41      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.21/1.41  thf(cc2_relset_1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.21/1.41  thf('110', plain,
% 1.21/1.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.21/1.41         ((v4_relat_1 @ X23 @ X24)
% 1.21/1.41          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.21/1.41  thf('111', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.21/1.41      inference('sup-', [status(thm)], ['109', '110'])).
% 1.21/1.41  thf('112', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['105', '108', '111'])).
% 1.21/1.41  thf(t187_relat_1, axiom,
% 1.21/1.41    (![A:$i]:
% 1.21/1.41     ( ( v1_relat_1 @ A ) =>
% 1.21/1.41       ( ![B:$i]:
% 1.21/1.41         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 1.21/1.41           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.21/1.41  thf('113', plain,
% 1.21/1.41      (![X12 : $i, X13 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X12 @ (k1_relat_1 @ X13))
% 1.21/1.41          | ((k7_relat_1 @ X13 @ X12) = (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ X13))),
% 1.21/1.41      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.21/1.41  thf('114', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.21/1.41          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.21/1.41          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['112', '113'])).
% 1.21/1.41  thf('115', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.21/1.41      inference('sup-', [status(thm)], ['106', '107'])).
% 1.21/1.41  thf('116', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.21/1.41          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('demod', [status(thm)], ['114', '115'])).
% 1.21/1.41  thf('117', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['94', '116'])).
% 1.21/1.41  thf('118', plain,
% 1.21/1.41      (![X16 : $i, X17 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 1.21/1.41            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 1.21/1.41          | ~ (v1_relat_1 @ X16))),
% 1.21/1.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.21/1.41  thf('119', plain,
% 1.21/1.41      ((((k1_relat_1 @ k1_xboole_0)
% 1.21/1.41          = (k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_C))
% 1.21/1.41        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.21/1.41      inference('sup+', [status(thm)], ['117', '118'])).
% 1.21/1.41  thf('120', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['105', '108', '111'])).
% 1.21/1.41  thf('121', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['105', '108', '111'])).
% 1.21/1.41  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.21/1.41      inference('sup-', [status(thm)], ['106', '107'])).
% 1.21/1.41  thf('123', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_C))),
% 1.21/1.41      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 1.21/1.41  thf('124', plain,
% 1.21/1.41      (![X0 : $i, X2 : $i]:
% 1.21/1.41         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.21/1.41      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.21/1.41  thf('125', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_C))),
% 1.21/1.41      inference('sup-', [status(thm)], ['123', '124'])).
% 1.21/1.41  thf('126', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_C)),
% 1.21/1.41      inference('simplify', [status(thm)], ['125'])).
% 1.21/1.41  thf('127', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(cc5_funct_2, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.41       ( ![C:$i]:
% 1.21/1.41         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.41           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.21/1.41             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.21/1.41  thf('128', plain,
% 1.21/1.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.21/1.41          | (v1_partfun1 @ X26 @ X27)
% 1.21/1.41          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 1.21/1.41          | ~ (v1_funct_1 @ X26)
% 1.21/1.41          | (v1_xboole_0 @ X28))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.21/1.41  thf('129', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ sk_E)
% 1.21/1.41        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 1.21/1.41        | (v1_partfun1 @ sk_E @ sk_C))),
% 1.21/1.41      inference('sup-', [status(thm)], ['127', '128'])).
% 1.21/1.41  thf('130', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('131', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('132', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_E @ sk_C))),
% 1.21/1.41      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.21/1.41  thf('133', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('134', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 1.21/1.41      inference('clc', [status(thm)], ['132', '133'])).
% 1.21/1.41  thf('135', plain,
% 1.21/1.41      (![X29 : $i, X30 : $i]:
% 1.21/1.41         (~ (v1_partfun1 @ X30 @ X29)
% 1.21/1.41          | ((k1_relat_1 @ X30) = (X29))
% 1.21/1.41          | ~ (v4_relat_1 @ X30 @ X29)
% 1.21/1.41          | ~ (v1_relat_1 @ X30))),
% 1.21/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.21/1.41  thf('136', plain,
% 1.21/1.41      ((~ (v1_relat_1 @ sk_E)
% 1.21/1.41        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 1.21/1.41        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['134', '135'])).
% 1.21/1.41  thf('137', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('138', plain,
% 1.21/1.41      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.21/1.41         ((v1_relat_1 @ X20)
% 1.21/1.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.21/1.41  thf('139', plain, ((v1_relat_1 @ sk_E)),
% 1.21/1.41      inference('sup-', [status(thm)], ['137', '138'])).
% 1.21/1.41  thf('140', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('141', plain,
% 1.21/1.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.21/1.41         ((v4_relat_1 @ X23 @ X24)
% 1.21/1.41          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.21/1.41  thf('142', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 1.21/1.41      inference('sup-', [status(thm)], ['140', '141'])).
% 1.21/1.41  thf('143', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.21/1.41      inference('demod', [status(thm)], ['136', '139', '142'])).
% 1.21/1.41  thf('144', plain,
% 1.21/1.41      (![X12 : $i, X13 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X12 @ (k1_relat_1 @ X13))
% 1.21/1.41          | ((k7_relat_1 @ X13 @ X12) = (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ X13))),
% 1.21/1.41      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.21/1.41  thf('145', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.21/1.41          | ~ (v1_relat_1 @ sk_E)
% 1.21/1.41          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['143', '144'])).
% 1.21/1.41  thf('146', plain, ((v1_relat_1 @ sk_E)),
% 1.21/1.41      inference('sup-', [status(thm)], ['137', '138'])).
% 1.21/1.41  thf('147', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.21/1.41          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('demod', [status(thm)], ['145', '146'])).
% 1.21/1.41  thf('148', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['126', '147'])).
% 1.21/1.41  thf('149', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.21/1.41  thf('150', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('151', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('152', plain,
% 1.21/1.41      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.21/1.41          | ~ (v1_funct_1 @ X31)
% 1.21/1.41          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 1.21/1.41      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.21/1.41  thf('153', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 1.21/1.41          | ~ (v1_funct_1 @ sk_F))),
% 1.21/1.41      inference('sup-', [status(thm)], ['151', '152'])).
% 1.21/1.41  thf('154', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('155', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['153', '154'])).
% 1.21/1.41  thf('156', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.21/1.41      inference('clc', [status(thm)], ['60', '61'])).
% 1.21/1.41  thf('157', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B @ X0)) = (X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.21/1.41  thf('158', plain,
% 1.21/1.41      (![X12 : $i, X13 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X12 @ (k1_relat_1 @ X13))
% 1.21/1.41          | ((k7_relat_1 @ X13 @ X12) = (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ X13))),
% 1.21/1.41      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.21/1.41  thf('159', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X1 @ X0)
% 1.21/1.41          | ~ (v1_relat_1 @ (sk_B @ X0))
% 1.21/1.41          | ((k7_relat_1 @ (sk_B @ X0) @ X1) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['157', '158'])).
% 1.21/1.41  thf('160', plain, (![X35 : $i]: (v1_relat_1 @ (sk_B @ X35))),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('161', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X1 @ X0)
% 1.21/1.41          | ((k7_relat_1 @ (sk_B @ X0) @ X1) = (k1_xboole_0)))),
% 1.21/1.41      inference('demod', [status(thm)], ['159', '160'])).
% 1.21/1.41  thf('162', plain, (((k7_relat_1 @ (sk_B @ sk_D) @ sk_C) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['156', '161'])).
% 1.21/1.41  thf('163', plain,
% 1.21/1.41      (![X16 : $i, X17 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 1.21/1.41            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 1.21/1.41          | ~ (v1_relat_1 @ X16))),
% 1.21/1.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.21/1.41  thf('164', plain,
% 1.21/1.41      ((((k1_relat_1 @ k1_xboole_0)
% 1.21/1.41          = (k3_xboole_0 @ (k1_relat_1 @ (sk_B @ sk_D)) @ sk_C))
% 1.21/1.41        | ~ (v1_relat_1 @ (sk_B @ sk_D)))),
% 1.21/1.41      inference('sup+', [status(thm)], ['162', '163'])).
% 1.21/1.41  thf('165', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['105', '108', '111'])).
% 1.21/1.41  thf('166', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B @ X0)) = (X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.21/1.41  thf('167', plain, (![X35 : $i]: (v1_relat_1 @ (sk_B @ X35))),
% 1.21/1.41      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.21/1.41  thf('168', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 1.21/1.41      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 1.21/1.41  thf('169', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k3_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 1.21/1.41          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.21/1.41  thf('170', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.41        | (r1_xboole_0 @ sk_D @ (k3_xboole_0 @ sk_D @ sk_C)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['168', '169'])).
% 1.21/1.41  thf('171', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_D @ sk_C))),
% 1.21/1.41      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 1.21/1.41  thf('172', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_D @ k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['170', '171'])).
% 1.21/1.41  thf('173', plain, ((r1_xboole_0 @ sk_D @ k1_xboole_0)),
% 1.21/1.41      inference('simplify', [status(thm)], ['172'])).
% 1.21/1.41  thf('174', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.21/1.41          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('demod', [status(thm)], ['114', '115'])).
% 1.21/1.41  thf('175', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['173', '174'])).
% 1.21/1.41  thf('176', plain,
% 1.21/1.41      (![X16 : $i, X17 : $i]:
% 1.21/1.41         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 1.21/1.41            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 1.21/1.41          | ~ (v1_relat_1 @ X16))),
% 1.21/1.41      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.21/1.41  thf('177', plain,
% 1.21/1.41      ((((k1_relat_1 @ k1_xboole_0)
% 1.21/1.41          = (k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_D))
% 1.21/1.41        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.21/1.41      inference('sup+', [status(thm)], ['175', '176'])).
% 1.21/1.41  thf('178', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['105', '108', '111'])).
% 1.21/1.41  thf('179', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('demod', [status(thm)], ['105', '108', '111'])).
% 1.21/1.41  thf('180', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.21/1.41      inference('sup-', [status(thm)], ['106', '107'])).
% 1.21/1.41  thf('181', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 1.21/1.41  thf('182', plain,
% 1.21/1.41      (![X0 : $i, X2 : $i]:
% 1.21/1.41         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.21/1.41      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.21/1.41  thf('183', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['181', '182'])).
% 1.21/1.41  thf('184', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_D)),
% 1.21/1.41      inference('simplify', [status(thm)], ['183'])).
% 1.21/1.41  thf('185', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('186', plain,
% 1.21/1.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.21/1.41          | (v1_partfun1 @ X26 @ X27)
% 1.21/1.41          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 1.21/1.41          | ~ (v1_funct_1 @ X26)
% 1.21/1.41          | (v1_xboole_0 @ X28))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.21/1.41  thf('187', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ sk_F)
% 1.21/1.41        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.21/1.41        | (v1_partfun1 @ sk_F @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['185', '186'])).
% 1.21/1.41  thf('188', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('189', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('190', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_F @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['187', '188', '189'])).
% 1.21/1.41  thf('191', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('192', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 1.21/1.41      inference('clc', [status(thm)], ['190', '191'])).
% 1.21/1.41  thf('193', plain,
% 1.21/1.41      (![X29 : $i, X30 : $i]:
% 1.21/1.41         (~ (v1_partfun1 @ X30 @ X29)
% 1.21/1.41          | ((k1_relat_1 @ X30) = (X29))
% 1.21/1.41          | ~ (v4_relat_1 @ X30 @ X29)
% 1.21/1.41          | ~ (v1_relat_1 @ X30))),
% 1.21/1.41      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.21/1.41  thf('194', plain,
% 1.21/1.41      ((~ (v1_relat_1 @ sk_F)
% 1.21/1.41        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 1.21/1.41        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['192', '193'])).
% 1.21/1.41  thf('195', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('196', plain,
% 1.21/1.41      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.21/1.41         ((v1_relat_1 @ X20)
% 1.21/1.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.21/1.41  thf('197', plain, ((v1_relat_1 @ sk_F)),
% 1.21/1.41      inference('sup-', [status(thm)], ['195', '196'])).
% 1.21/1.41  thf('198', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('199', plain,
% 1.21/1.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.21/1.41         ((v4_relat_1 @ X23 @ X24)
% 1.21/1.41          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.21/1.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.21/1.41  thf('200', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 1.21/1.41      inference('sup-', [status(thm)], ['198', '199'])).
% 1.21/1.41  thf('201', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['194', '197', '200'])).
% 1.21/1.41  thf('202', plain,
% 1.21/1.41      (![X12 : $i, X13 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X12 @ (k1_relat_1 @ X13))
% 1.21/1.41          | ((k7_relat_1 @ X13 @ X12) = (k1_xboole_0))
% 1.21/1.41          | ~ (v1_relat_1 @ X13))),
% 1.21/1.41      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.21/1.41  thf('203', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ sk_D)
% 1.21/1.41          | ~ (v1_relat_1 @ sk_F)
% 1.21/1.41          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['201', '202'])).
% 1.21/1.41  thf('204', plain, ((v1_relat_1 @ sk_F)),
% 1.21/1.41      inference('sup-', [status(thm)], ['195', '196'])).
% 1.21/1.41  thf('205', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (r1_xboole_0 @ X0 @ sk_D)
% 1.21/1.41          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 1.21/1.41      inference('demod', [status(thm)], ['203', '204'])).
% 1.21/1.41  thf('206', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['184', '205'])).
% 1.21/1.41  thf('207', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('208', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('209', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('210', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('211', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41            = (sk_E))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_A))),
% 1.21/1.41      inference('demod', [status(thm)],
% 1.21/1.41                ['48', '49', '50', '51', '52', '55', '64', '69', '148', '149', 
% 1.21/1.41                 '150', '155', '206', '207', '208', '209', '210'])).
% 1.21/1.41  thf('212', plain,
% 1.21/1.41      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41            = (sk_E))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify', [status(thm)], ['211'])).
% 1.21/1.41  thf('213', plain,
% 1.21/1.41      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41            != (sk_E))
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            != (sk_F)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('214', plain,
% 1.21/1.41      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41          != (sk_E)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41                = (sk_E))))),
% 1.21/1.41      inference('split', [status(esa)], ['213'])).
% 1.21/1.41  thf('215', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['153', '154'])).
% 1.21/1.41  thf('216', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.21/1.41  thf('217', plain,
% 1.21/1.41      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.21/1.41      inference('split', [status(esa)], ['213'])).
% 1.21/1.41  thf('218', plain,
% 1.21/1.41      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['216', '217'])).
% 1.21/1.41  thf('219', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.21/1.41  thf('220', plain,
% 1.21/1.41      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 1.21/1.41          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.21/1.41      inference('demod', [status(thm)], ['218', '219'])).
% 1.21/1.41  thf('221', plain,
% 1.21/1.41      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 1.21/1.41          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['215', '220'])).
% 1.21/1.41  thf('222', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('223', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['67', '68'])).
% 1.21/1.41  thf('224', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['126', '147'])).
% 1.21/1.41  thf('225', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('226', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['184', '205'])).
% 1.21/1.41  thf('227', plain,
% 1.21/1.41      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.21/1.41      inference('demod', [status(thm)],
% 1.21/1.41                ['221', '222', '223', '224', '225', '226'])).
% 1.21/1.41  thf('228', plain,
% 1.21/1.41      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 1.21/1.41      inference('simplify', [status(thm)], ['227'])).
% 1.21/1.41  thf('229', plain,
% 1.21/1.41      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['13', '14'])).
% 1.21/1.41  thf('230', plain,
% 1.21/1.41      (((v1_funct_2 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['28', '29'])).
% 1.21/1.41  thf('231', plain,
% 1.21/1.41      (((m1_subset_1 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41         (k1_zfmisc_1 @ 
% 1.21/1.41          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['43', '44'])).
% 1.21/1.41  thf('232', plain,
% 1.21/1.41      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.21/1.41         ((v1_xboole_0 @ X37)
% 1.21/1.41          | (v1_xboole_0 @ X38)
% 1.21/1.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | ~ (v1_funct_1 @ X40)
% 1.21/1.41          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 1.21/1.41          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.21/1.41          | ((X43) != (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 1.21/1.41          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ X43 @ X38)
% 1.21/1.41              = (X40))
% 1.21/1.41          | ~ (m1_subset_1 @ X43 @ 
% 1.21/1.41               (k1_zfmisc_1 @ 
% 1.21/1.41                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 1.21/1.41          | ~ (v1_funct_2 @ X43 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 1.21/1.41          | ~ (v1_funct_1 @ X43)
% 1.21/1.41          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 1.21/1.41              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 1.21/1.41                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 1.21/1.41          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 1.21/1.41          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 1.21/1.41          | ~ (v1_funct_1 @ X41)
% 1.21/1.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | (v1_xboole_0 @ X42)
% 1.21/1.41          | (v1_xboole_0 @ X39))),
% 1.21/1.41      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.21/1.41  thf('233', plain,
% 1.21/1.41      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.21/1.41         ((v1_xboole_0 @ X39)
% 1.21/1.41          | (v1_xboole_0 @ X42)
% 1.21/1.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | ~ (v1_funct_1 @ X41)
% 1.21/1.41          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 1.21/1.41          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 1.21/1.41          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 1.21/1.41              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 1.21/1.41                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 1.21/1.41          | ~ (v1_funct_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 1.21/1.41          | ~ (v1_funct_2 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 1.21/1.41               (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 1.21/1.41          | ~ (m1_subset_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 1.21/1.41               (k1_zfmisc_1 @ 
% 1.21/1.41                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 1.21/1.41          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ 
% 1.21/1.41              (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ X38) = (
% 1.21/1.41              X40))
% 1.21/1.41          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.21/1.41          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 1.21/1.41          | ~ (v1_funct_1 @ X40)
% 1.21/1.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.21/1.41          | (v1_xboole_0 @ X38)
% 1.21/1.41          | (v1_xboole_0 @ X37))),
% 1.21/1.41      inference('simplify', [status(thm)], ['232'])).
% 1.21/1.41  thf('234', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | ~ (v1_funct_1 @ sk_F)
% 1.21/1.41        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            = (sk_F))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.21/1.41        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 1.21/1.41        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ sk_E)
% 1.21/1.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_A))),
% 1.21/1.41      inference('sup-', [status(thm)], ['231', '233'])).
% 1.21/1.41  thf('235', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('236', plain, ((v1_funct_1 @ sk_F)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('237', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('238', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('239', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.21/1.41  thf('240', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('241', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['67', '68'])).
% 1.21/1.41  thf('242', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['126', '147'])).
% 1.21/1.41  thf('243', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.21/1.41  thf('244', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['62', '63'])).
% 1.21/1.41  thf('245', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.21/1.41      inference('demod', [status(thm)], ['153', '154'])).
% 1.21/1.41  thf('246', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.41      inference('sup-', [status(thm)], ['184', '205'])).
% 1.21/1.41  thf('247', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('248', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('249', plain, ((v1_funct_1 @ sk_E)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('250', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('251', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            = (sk_F))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | ~ (v1_funct_1 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_A))),
% 1.21/1.41      inference('demod', [status(thm)],
% 1.21/1.41                ['234', '235', '236', '237', '238', '239', '240', '241', 
% 1.21/1.41                 '242', '243', '244', '245', '246', '247', '248', '249', '250'])).
% 1.21/1.41  thf('252', plain,
% 1.21/1.41      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            = (sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify', [status(thm)], ['251'])).
% 1.21/1.41  thf('253', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            = (sk_F))
% 1.21/1.41        | ~ (v1_funct_1 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['230', '252'])).
% 1.21/1.41  thf('254', plain,
% 1.21/1.41      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            = (sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify', [status(thm)], ['253'])).
% 1.21/1.41  thf('255', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41            = (sk_F)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['229', '254'])).
% 1.21/1.41  thf('256', plain,
% 1.21/1.41      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41          = (sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify', [status(thm)], ['255'])).
% 1.21/1.41  thf('257', plain,
% 1.21/1.41      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41          != (sk_F)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41                = (sk_F))))),
% 1.21/1.41      inference('split', [status(esa)], ['213'])).
% 1.21/1.41  thf('258', plain,
% 1.21/1.41      (((((sk_F) != (sk_F))
% 1.21/1.41         | (v1_xboole_0 @ sk_D)
% 1.21/1.41         | (v1_xboole_0 @ sk_C)
% 1.21/1.41         | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41         | (v1_xboole_0 @ sk_A)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41                = (sk_F))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['256', '257'])).
% 1.21/1.41  thf('259', plain,
% 1.21/1.41      ((((v1_xboole_0 @ sk_A)
% 1.21/1.41         | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41         | (v1_xboole_0 @ sk_C)
% 1.21/1.41         | (v1_xboole_0 @ sk_D)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41                = (sk_F))))),
% 1.21/1.41      inference('simplify', [status(thm)], ['258'])).
% 1.21/1.41  thf('260', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('261', plain,
% 1.21/1.41      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41                = (sk_F))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['259', '260'])).
% 1.21/1.41  thf('262', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('263', plain,
% 1.21/1.41      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41                = (sk_F))))),
% 1.21/1.41      inference('clc', [status(thm)], ['261', '262'])).
% 1.21/1.41  thf('264', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('265', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_B_1))
% 1.21/1.41         <= (~
% 1.21/1.41             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41                = (sk_F))))),
% 1.21/1.41      inference('clc', [status(thm)], ['263', '264'])).
% 1.21/1.41  thf('266', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('267', plain,
% 1.21/1.41      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41          = (sk_F)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['265', '266'])).
% 1.21/1.41  thf('268', plain,
% 1.21/1.41      (~
% 1.21/1.41       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41          = (sk_E))) | 
% 1.21/1.41       ~
% 1.21/1.41       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.21/1.41          = (sk_F))) | 
% 1.21/1.41       ~
% 1.21/1.41       (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.21/1.41          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.21/1.41          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.21/1.41             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 1.21/1.41      inference('split', [status(esa)], ['213'])).
% 1.21/1.41  thf('269', plain,
% 1.21/1.41      (~
% 1.21/1.41       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41          = (sk_E)))),
% 1.21/1.41      inference('sat_resolution*', [status(thm)], ['228', '267', '268'])).
% 1.21/1.41  thf('270', plain,
% 1.21/1.41      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.21/1.41         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.21/1.41         != (sk_E))),
% 1.21/1.41      inference('simpl_trail', [status(thm)], ['214', '269'])).
% 1.21/1.41  thf('271', plain,
% 1.21/1.41      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | ~ (v1_funct_2 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.21/1.41             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify_reflect-', [status(thm)], ['212', '270'])).
% 1.21/1.41  thf('272', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | ~ (v1_funct_1 @ 
% 1.21/1.41             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['30', '271'])).
% 1.21/1.41  thf('273', plain,
% 1.21/1.41      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify', [status(thm)], ['272'])).
% 1.21/1.41  thf('274', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_D)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_A))),
% 1.21/1.41      inference('sup-', [status(thm)], ['15', '273'])).
% 1.21/1.41  thf('275', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_A)
% 1.21/1.41        | (v1_xboole_0 @ sk_B_1)
% 1.21/1.41        | (v1_xboole_0 @ sk_C)
% 1.21/1.41        | (v1_xboole_0 @ sk_D))),
% 1.21/1.41      inference('simplify', [status(thm)], ['274'])).
% 1.21/1.41  thf('276', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('277', plain,
% 1.21/1.41      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 1.21/1.41      inference('sup-', [status(thm)], ['275', '276'])).
% 1.21/1.41  thf('278', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('279', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 1.21/1.41      inference('clc', [status(thm)], ['277', '278'])).
% 1.21/1.41  thf('280', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('281', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.21/1.41      inference('clc', [status(thm)], ['279', '280'])).
% 1.21/1.41  thf('282', plain, ($false), inference('demod', [status(thm)], ['0', '281'])).
% 1.21/1.41  
% 1.21/1.41  % SZS output end Refutation
% 1.21/1.41  
% 1.21/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
