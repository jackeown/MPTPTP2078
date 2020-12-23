%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGn0DIqwtR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:57 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  275 (1770 expanded)
%              Number of leaves         :   47 ( 545 expanded)
%              Depth                    :   36
%              Number of atoms          : 3815 (61070 expanded)
%              Number of equality atoms :  142 (2067 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X50 @ X48 @ X47 @ X49 @ X46 @ X51 ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X50 @ X48 @ X47 @ X49 @ X46 @ X51 ) @ ( k4_subset_1 @ X50 @ X47 @ X49 ) @ X48 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X50 ) )
      | ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X50 @ X48 @ X47 @ X49 @ X46 @ X51 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X50 @ X47 @ X49 ) @ X48 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( X45
       != ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 @ X45 @ X44 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X44 @ X39 @ X43 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) )
       != ( k2_partfun1 @ X40 @ X39 @ X42 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X39 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X39 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X39 ) ) )
      | ( ( k2_partfun1 @ X44 @ X39 @ X43 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) )
       != ( k2_partfun1 @ X40 @ X39 @ X42 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) @ X44 )
        = X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X39 ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_subset_1 @ X3 @ X1 @ X2 )
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('66',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_relat_1 @ sk_F )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_F @ sk_D ) @ ( k9_relat_1 @ sk_F @ sk_D ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_F @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('70',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('71',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('72',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('74',plain,
    ( ( ( k2_relat_1 @ sk_F )
      = ( k9_relat_1 @ sk_F @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_F )
    = ( k9_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('78',plain,
    ( ( k10_relat_1 @ sk_F @ ( k2_relat_1 @ sk_F ) )
    = ( k1_relat_1 @ sk_F ) ),
    inference(demod,[status(thm)],['68','69','70','71','76','77'])).

thf('79',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('80',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
       => ( r1_subset_1 @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( r1_subset_1 @ X20 @ X19 )
      | ~ ( r1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_subset_1])).

thf('82',plain,
    ( ( r1_subset_1 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_subset_1 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_subset_1 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['84','85'])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('88',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(clc,[status(thm)],['90','91'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('93',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X12 ) @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_D ) @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k7_relat_1 @ sk_F @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['79','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('97',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('98',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k3_xboole_0 @ X21 @ ( k10_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = ( k3_xboole_0 @ sk_C @ ( k10_relat_1 @ sk_F @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('100',plain,(
    ! [X11: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('101',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('102',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k10_relat_1 @ sk_F @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['78','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
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

thf('105',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('106',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['109','110'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('112',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X34 @ X33 )
      | ( ( k1_relat_1 @ X34 )
        = X33 )
      | ~ ( v4_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('115',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('119',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('130',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['127','130'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('132',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('133',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X12 ) @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['128','129'])).

thf('137',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('139',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('140',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('147',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['61','62'])).

thf('149',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','117','122','137','138','139','144','149','150','151','152','153'])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
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
    inference('sup-',[status(thm)],['30','155'])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('161',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('162',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['158'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('165',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['161','165'])).

thf('167',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('168',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('171',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','136'])).

thf('172',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['147','148'])).

thf('173',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('176',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('177',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('178',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ( X45
       != ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 @ X45 @ X40 )
        = X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 )
      | ~ ( v1_funct_1 @ X45 )
      | ( ( k2_partfun1 @ X44 @ X39 @ X43 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) )
       != ( k2_partfun1 @ X40 @ X39 @ X42 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X39 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('179',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X39 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X39 ) ) )
      | ( ( k2_partfun1 @ X44 @ X39 @ X43 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) )
       != ( k2_partfun1 @ X40 @ X39 @ X42 @ ( k9_subset_1 @ X41 @ X44 @ X40 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X41 @ X44 @ X40 ) @ X39 @ ( k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42 ) @ X40 )
        = X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
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
    inference('sup-',[status(thm)],['177','179'])).

thf('181',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('186',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('188',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','136'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('190',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('192',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['147','148'])).

thf('193',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
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
    inference(demod,[status(thm)],['180','181','182','183','184','185','186','187','188','189','190','191','192','193','194','195','196'])).

thf('198',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
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
    inference('sup-',[status(thm)],['176','198'])).

thf('200',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
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
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['175','200'])).

thf('202',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['158'])).

thf('204',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['158'])).

thf('215',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['174','213','214'])).

thf('216',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['159','215'])).

thf('217',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['157','216'])).

thf('218',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','217'])).

thf('219',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    $false ),
    inference(demod,[status(thm)],['0','225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGn0DIqwtR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 418 iterations in 0.243s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.48/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.70  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.48/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.48/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.48/0.70  thf(sk_F_type, type, sk_F: $i).
% 0.48/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.70  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.48/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.48/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.48/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.48/0.70  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.70  thf(t6_tmap_1, conjecture,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.70           ( ![C:$i]:
% 0.48/0.70             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.70                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70               ( ![D:$i]:
% 0.48/0.70                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70                   ( ( r1_subset_1 @ C @ D ) =>
% 0.48/0.70                     ( ![E:$i]:
% 0.48/0.70                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.70                           ( m1_subset_1 @
% 0.48/0.70                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.48/0.70                         ( ![F:$i]:
% 0.48/0.70                           ( ( ( v1_funct_1 @ F ) & 
% 0.48/0.70                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.70                               ( m1_subset_1 @
% 0.48/0.70                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.70                             ( ( ( k2_partfun1 @
% 0.48/0.70                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.48/0.70                                 ( k2_partfun1 @
% 0.48/0.70                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.48/0.70                               ( ( k2_partfun1 @
% 0.48/0.70                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.70                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.48/0.70                                 ( E ) ) & 
% 0.48/0.70                               ( ( k2_partfun1 @
% 0.48/0.70                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.70                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.48/0.70                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i]:
% 0.48/0.70        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.70          ( ![B:$i]:
% 0.48/0.70            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.70              ( ![C:$i]:
% 0.48/0.70                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.70                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70                  ( ![D:$i]:
% 0.48/0.70                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.70                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70                      ( ( r1_subset_1 @ C @ D ) =>
% 0.48/0.70                        ( ![E:$i]:
% 0.48/0.70                          ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.70                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.70                              ( m1_subset_1 @
% 0.48/0.70                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.48/0.70                            ( ![F:$i]:
% 0.48/0.70                              ( ( ( v1_funct_1 @ F ) & 
% 0.48/0.70                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.70                                  ( m1_subset_1 @
% 0.48/0.70                                    F @ 
% 0.48/0.70                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.70                                ( ( ( k2_partfun1 @
% 0.48/0.70                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.48/0.70                                    ( k2_partfun1 @
% 0.48/0.70                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.48/0.70                                  ( ( k2_partfun1 @
% 0.48/0.70                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.70                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.48/0.70                                    ( E ) ) & 
% 0.48/0.70                                  ( ( k2_partfun1 @
% 0.48/0.70                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.48/0.70                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.48/0.70                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.48/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('2', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('3', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(dt_k1_tmap_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.48/0.70         ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.48/0.70         ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.48/0.70         ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.48/0.70         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.70       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.48/0.70         ( v1_funct_2 @
% 0.48/0.70           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.48/0.70           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.48/0.70         ( m1_subset_1 @
% 0.48/0.70           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.48/0.70           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.48/0.70  thf('4', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.48/0.70          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.48/0.70          | ~ (v1_funct_1 @ X46)
% 0.48/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 0.48/0.70          | (v1_xboole_0 @ X49)
% 0.48/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X50))
% 0.48/0.70          | (v1_xboole_0 @ X47)
% 0.48/0.70          | (v1_xboole_0 @ X48)
% 0.48/0.70          | (v1_xboole_0 @ X50)
% 0.48/0.70          | ~ (v1_funct_1 @ X51)
% 0.48/0.70          | ~ (v1_funct_2 @ X51 @ X49 @ X48)
% 0.48/0.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.48/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X50 @ X48 @ X47 @ X49 @ X46 @ X51)))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.48/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.48/0.70          | ~ (v1_funct_1 @ X0)
% 0.48/0.70          | (v1_xboole_0 @ X2)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.48/0.70          | (v1_xboole_0 @ X1)
% 0.48/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.48/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.48/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.48/0.70  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('8', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.48/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.48/0.70          | ~ (v1_funct_1 @ X0)
% 0.48/0.70          | (v1_xboole_0 @ X2)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.48/0.70          | (v1_xboole_0 @ X1)
% 0.48/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.48/0.70      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_D)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.48/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.48/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['2', '8'])).
% 0.48/0.70  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_D)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.70      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.48/0.70  thf('13', plain,
% 0.48/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.70        | (v1_xboole_0 @ sk_D))),
% 0.48/0.70      inference('sup-', [status(thm)], ['1', '12'])).
% 0.48/0.70  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('15', plain,
% 0.48/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.70  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.48/0.70          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.48/0.70          | ~ (v1_funct_1 @ X46)
% 0.48/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 0.48/0.70          | (v1_xboole_0 @ X49)
% 0.48/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X50))
% 0.48/0.70          | (v1_xboole_0 @ X47)
% 0.48/0.70          | (v1_xboole_0 @ X48)
% 0.48/0.70          | (v1_xboole_0 @ X50)
% 0.48/0.70          | ~ (v1_funct_1 @ X51)
% 0.48/0.70          | ~ (v1_funct_2 @ X51 @ X49 @ X48)
% 0.48/0.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.48/0.70          | (v1_funct_2 @ (k1_tmap_1 @ X50 @ X48 @ X47 @ X49 @ X46 @ X51) @ 
% 0.48/0.70             (k4_subset_1 @ X50 @ X47 @ X49) @ X48))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.48/0.70  thf('20', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.48/0.70           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.48/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.48/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.48/0.70          | ~ (v1_funct_1 @ X2)
% 0.48/0.70          | (v1_xboole_0 @ X1)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.48/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.48/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.70  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('23', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.48/0.70           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.48/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.48/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.48/0.70          | ~ (v1_funct_1 @ X2)
% 0.48/0.70          | (v1_xboole_0 @ X1)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.70      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_D)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.48/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.48/0.70          | (v1_funct_2 @ 
% 0.48/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['17', '23'])).
% 0.48/0.70  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('27', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_D)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | (v1_funct_2 @ 
% 0.48/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.48/0.70      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.70        | (v1_xboole_0 @ sk_D))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '27'])).
% 0.48/0.70  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('30', plain,
% 0.48/0.70      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.70  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('32', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('34', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.48/0.70          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.48/0.70          | ~ (v1_funct_1 @ X46)
% 0.48/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 0.48/0.70          | (v1_xboole_0 @ X49)
% 0.48/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X50))
% 0.48/0.70          | (v1_xboole_0 @ X47)
% 0.48/0.70          | (v1_xboole_0 @ X48)
% 0.48/0.70          | (v1_xboole_0 @ X50)
% 0.48/0.70          | ~ (v1_funct_1 @ X51)
% 0.48/0.70          | ~ (v1_funct_2 @ X51 @ X49 @ X48)
% 0.48/0.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.48/0.70          | (m1_subset_1 @ (k1_tmap_1 @ X50 @ X48 @ X47 @ X49 @ X46 @ X51) @ 
% 0.48/0.70             (k1_zfmisc_1 @ 
% 0.48/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X50 @ X47 @ X49) @ X48))))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.48/0.70  thf('35', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.48/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.48/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.48/0.70          | ~ (v1_funct_1 @ X2)
% 0.48/0.70          | (v1_xboole_0 @ X1)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.48/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.48/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.48/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.70  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.48/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.48/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.48/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.48/0.70          | ~ (v1_funct_1 @ X2)
% 0.48/0.70          | (v1_xboole_0 @ X1)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.70      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_D)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.48/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.48/0.70          | (m1_subset_1 @ 
% 0.48/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70             (k1_zfmisc_1 @ 
% 0.48/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['32', '38'])).
% 0.48/0.70  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_D)
% 0.48/0.70          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.48/0.70          | (v1_xboole_0 @ sk_C)
% 0.48/0.70          | (v1_xboole_0 @ sk_B)
% 0.48/0.70          | (v1_xboole_0 @ X0)
% 0.48/0.70          | (m1_subset_1 @ 
% 0.48/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70             (k1_zfmisc_1 @ 
% 0.48/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.48/0.70      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.48/0.70  thf('43', plain,
% 0.48/0.70      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70         (k1_zfmisc_1 @ 
% 0.48/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.70        | (v1_xboole_0 @ sk_D))),
% 0.48/0.70      inference('sup-', [status(thm)], ['31', '42'])).
% 0.48/0.70  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70         (k1_zfmisc_1 @ 
% 0.48/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.48/0.70  thf(d1_tmap_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.70           ( ![C:$i]:
% 0.48/0.70             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.48/0.70                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70               ( ![D:$i]:
% 0.48/0.70                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.48/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.70                   ( ![E:$i]:
% 0.48/0.70                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.48/0.70                         ( m1_subset_1 @
% 0.48/0.70                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.48/0.70                       ( ![F:$i]:
% 0.48/0.70                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.48/0.70                             ( m1_subset_1 @
% 0.48/0.70                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.48/0.70                           ( ( ( k2_partfun1 @
% 0.48/0.70                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.48/0.70                               ( k2_partfun1 @
% 0.48/0.70                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.48/0.70                             ( ![G:$i]:
% 0.48/0.70                               ( ( ( v1_funct_1 @ G ) & 
% 0.48/0.70                                   ( v1_funct_2 @
% 0.48/0.70                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.48/0.70                                   ( m1_subset_1 @
% 0.48/0.70                                     G @ 
% 0.48/0.70                                     ( k1_zfmisc_1 @
% 0.48/0.70                                       ( k2_zfmisc_1 @
% 0.48/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.48/0.70                                 ( ( ( G ) =
% 0.48/0.70                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.48/0.70                                   ( ( ( k2_partfun1 @
% 0.48/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.48/0.70                                         C ) =
% 0.48/0.70                                       ( E ) ) & 
% 0.48/0.70                                     ( ( k2_partfun1 @
% 0.48/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.48/0.70                                         D ) =
% 0.48/0.70                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ X39)
% 0.48/0.70          | (v1_xboole_0 @ X40)
% 0.48/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.48/0.70          | ~ (v1_funct_1 @ X42)
% 0.48/0.70          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.48/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.48/0.70          | ((X45) != (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42))
% 0.48/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39 @ X45 @ X44)
% 0.48/0.70              = (X43))
% 0.48/0.70          | ~ (m1_subset_1 @ X45 @ 
% 0.48/0.70               (k1_zfmisc_1 @ 
% 0.48/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39)))
% 0.48/0.70          | ~ (v1_funct_2 @ X45 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39)
% 0.48/0.70          | ~ (v1_funct_1 @ X45)
% 0.48/0.70          | ((k2_partfun1 @ X44 @ X39 @ X43 @ (k9_subset_1 @ X41 @ X44 @ X40))
% 0.48/0.70              != (k2_partfun1 @ X40 @ X39 @ X42 @ 
% 0.48/0.70                  (k9_subset_1 @ X41 @ X44 @ X40)))
% 0.48/0.70          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X39)))
% 0.48/0.70          | ~ (v1_funct_2 @ X43 @ X44 @ X39)
% 0.48/0.70          | ~ (v1_funct_1 @ X43)
% 0.48/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X41))
% 0.48/0.70          | (v1_xboole_0 @ X44)
% 0.48/0.70          | (v1_xboole_0 @ X41))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.48/0.70  thf('47', plain,
% 0.48/0.70      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ X41)
% 0.48/0.70          | (v1_xboole_0 @ X44)
% 0.48/0.70          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X41))
% 0.48/0.70          | ~ (v1_funct_1 @ X43)
% 0.48/0.70          | ~ (v1_funct_2 @ X43 @ X44 @ X39)
% 0.48/0.70          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X39)))
% 0.48/0.70          | ((k2_partfun1 @ X44 @ X39 @ X43 @ (k9_subset_1 @ X41 @ X44 @ X40))
% 0.48/0.70              != (k2_partfun1 @ X40 @ X39 @ X42 @ 
% 0.48/0.70                  (k9_subset_1 @ X41 @ X44 @ X40)))
% 0.48/0.70          | ~ (v1_funct_1 @ (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42))
% 0.48/0.70          | ~ (v1_funct_2 @ (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42) @ 
% 0.48/0.70               (k4_subset_1 @ X41 @ X44 @ X40) @ X39)
% 0.48/0.70          | ~ (m1_subset_1 @ (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42) @ 
% 0.48/0.70               (k1_zfmisc_1 @ 
% 0.48/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39)))
% 0.48/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39 @ 
% 0.48/0.70              (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42) @ X44) = (
% 0.48/0.70              X43))
% 0.48/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.48/0.70          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.48/0.70          | ~ (v1_funct_1 @ X42)
% 0.48/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.48/0.70          | (v1_xboole_0 @ X40)
% 0.48/0.70          | (v1_xboole_0 @ X39))),
% 0.48/0.70      inference('simplify', [status(thm)], ['46'])).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (((v1_xboole_0 @ sk_D)
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_A)
% 0.48/0.70        | (v1_xboole_0 @ sk_B)
% 0.48/0.70        | (v1_xboole_0 @ sk_D)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.70        | ~ (v1_funct_1 @ sk_F)
% 0.48/0.70        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.48/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.70            = (sk_E))
% 0.48/0.70        | ~ (v1_funct_2 @ 
% 0.48/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.70             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.70        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.70        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.70            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.70            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.70                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.48/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.48/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.48/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.48/0.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.70        | (v1_xboole_0 @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_A))),
% 0.48/0.70      inference('sup-', [status(thm)], ['45', '47'])).
% 0.48/0.70  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(redefinition_k9_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.70       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.48/0.70  thf('54', plain,
% 0.48/0.70      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.70         (((k9_subset_1 @ X3 @ X1 @ X2) = (k3_xboole_0 @ X1 @ X2))
% 0.48/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.48/0.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(cc2_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.70  thf('57', plain,
% 0.48/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.70         ((v4_relat_1 @ X27 @ X28)
% 0.48/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.70  thf('58', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.48/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.70  thf(t209_relat_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.48/0.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.48/0.70  thf('59', plain,
% 0.48/0.70      (![X15 : $i, X16 : $i]:
% 0.48/0.70         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.48/0.70          | ~ (v4_relat_1 @ X15 @ X16)
% 0.48/0.70          | ~ (v1_relat_1 @ X15))),
% 0.48/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.70  thf('60', plain,
% 0.48/0.70      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.48/0.70  thf('61', plain,
% 0.48/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(cc1_relset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.70       ( v1_relat_1 @ C ) ))).
% 0.48/0.70  thf('62', plain,
% 0.48/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.70         ((v1_relat_1 @ X24)
% 0.48/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.70  thf('63', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.70  thf('64', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['60', '63'])).
% 0.48/0.70  thf(t148_relat_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ B ) =>
% 0.48/0.70       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.48/0.70  thf('65', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i]:
% 0.48/0.70         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.48/0.70          | ~ (v1_relat_1 @ X8))),
% 0.48/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.70  thf(t169_relat_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.48/0.70  thf('66', plain,
% 0.48/0.70      (![X10 : $i]:
% 0.48/0.70         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.48/0.70          | ~ (v1_relat_1 @ X10))),
% 0.48/0.70      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.48/0.70  thf('67', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.48/0.70            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.48/0.70          | ~ (v1_relat_1 @ X1)
% 0.48/0.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['65', '66'])).
% 0.48/0.70  thf('68', plain,
% 0.48/0.70      ((~ (v1_relat_1 @ sk_F)
% 0.48/0.70        | ~ (v1_relat_1 @ sk_F)
% 0.48/0.70        | ((k10_relat_1 @ (k7_relat_1 @ sk_F @ sk_D) @ 
% 0.48/0.70            (k9_relat_1 @ sk_F @ sk_D))
% 0.48/0.70            = (k1_relat_1 @ (k7_relat_1 @ sk_F @ sk_D))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['64', '67'])).
% 0.48/0.70  thf('69', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.70  thf('70', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.70  thf('71', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['60', '63'])).
% 0.48/0.70  thf('72', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['60', '63'])).
% 0.48/0.70  thf('73', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i]:
% 0.48/0.70         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.48/0.70          | ~ (v1_relat_1 @ X8))),
% 0.48/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.48/0.70  thf('74', plain,
% 0.48/0.70      ((((k2_relat_1 @ sk_F) = (k9_relat_1 @ sk_F @ sk_D))
% 0.48/0.70        | ~ (v1_relat_1 @ sk_F))),
% 0.48/0.70      inference('sup+', [status(thm)], ['72', '73'])).
% 0.48/0.70  thf('75', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.70  thf('76', plain, (((k2_relat_1 @ sk_F) = (k9_relat_1 @ sk_F @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['74', '75'])).
% 0.48/0.70  thf('77', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['60', '63'])).
% 0.48/0.70  thf('78', plain,
% 0.48/0.70      (((k10_relat_1 @ sk_F @ (k2_relat_1 @ sk_F)) = (k1_relat_1 @ sk_F))),
% 0.48/0.70      inference('demod', [status(thm)], ['68', '69', '70', '71', '76', '77'])).
% 0.48/0.70  thf('79', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.70      inference('demod', [status(thm)], ['60', '63'])).
% 0.48/0.70  thf('80', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(symmetry_r1_subset_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.48/0.70       ( ( r1_subset_1 @ A @ B ) => ( r1_subset_1 @ B @ A ) ) ))).
% 0.48/0.70  thf('81', plain,
% 0.48/0.70      (![X19 : $i, X20 : $i]:
% 0.48/0.70         ((v1_xboole_0 @ X19)
% 0.48/0.70          | (v1_xboole_0 @ X20)
% 0.48/0.70          | (r1_subset_1 @ X20 @ X19)
% 0.48/0.70          | ~ (r1_subset_1 @ X19 @ X20))),
% 0.48/0.70      inference('cnf', [status(esa)], [symmetry_r1_subset_1])).
% 0.48/0.70  thf('82', plain,
% 0.48/0.70      (((r1_subset_1 @ sk_D @ sk_C)
% 0.48/0.70        | (v1_xboole_0 @ sk_D)
% 0.48/0.70        | (v1_xboole_0 @ sk_C))),
% 0.48/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.48/0.70  thf('83', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('84', plain, (((v1_xboole_0 @ sk_C) | (r1_subset_1 @ sk_D @ sk_C))),
% 0.48/0.71      inference('clc', [status(thm)], ['82', '83'])).
% 0.48/0.71  thf('85', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('86', plain, ((r1_subset_1 @ sk_D @ sk_C)),
% 0.48/0.71      inference('clc', [status(thm)], ['84', '85'])).
% 0.48/0.71  thf(redefinition_r1_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.48/0.71       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.48/0.71  thf('87', plain,
% 0.48/0.71      (![X17 : $i, X18 : $i]:
% 0.48/0.71         ((v1_xboole_0 @ X17)
% 0.48/0.71          | (v1_xboole_0 @ X18)
% 0.48/0.71          | (r1_xboole_0 @ X17 @ X18)
% 0.48/0.71          | ~ (r1_subset_1 @ X17 @ X18))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.48/0.71  thf('88', plain,
% 0.48/0.71      (((r1_xboole_0 @ sk_D @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['86', '87'])).
% 0.48/0.71  thf('89', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('90', plain, (((v1_xboole_0 @ sk_D) | (r1_xboole_0 @ sk_D @ sk_C))),
% 0.48/0.71      inference('clc', [status(thm)], ['88', '89'])).
% 0.48/0.71  thf('91', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('92', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.48/0.71      inference('clc', [status(thm)], ['90', '91'])).
% 0.48/0.71  thf(t207_relat_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ C ) =>
% 0.48/0.71       ( ( r1_xboole_0 @ A @ B ) =>
% 0.48/0.71         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.71  thf('93', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.71         (~ (r1_xboole_0 @ X12 @ X13)
% 0.48/0.71          | ~ (v1_relat_1 @ X14)
% 0.48/0.71          | ((k7_relat_1 @ (k7_relat_1 @ X14 @ X12) @ X13) = (k1_xboole_0)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.48/0.71  thf('94', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_D) @ sk_C) = (k1_xboole_0))
% 0.48/0.71          | ~ (v1_relat_1 @ X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['92', '93'])).
% 0.48/0.71  thf('95', plain,
% 0.48/0.71      ((((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_F))),
% 0.48/0.71      inference('sup+', [status(thm)], ['79', '94'])).
% 0.48/0.71  thf('96', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.71  thf('97', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['95', '96'])).
% 0.48/0.71  thf(t139_funct_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( v1_relat_1 @ C ) =>
% 0.48/0.71       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.48/0.71         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.48/0.71  thf('98', plain,
% 0.48/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.71         (((k10_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X23)
% 0.48/0.71            = (k3_xboole_0 @ X21 @ (k10_relat_1 @ X22 @ X23)))
% 0.48/0.71          | ~ (v1_relat_1 @ X22))),
% 0.48/0.71      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.48/0.71  thf('99', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.48/0.71            = (k3_xboole_0 @ sk_C @ (k10_relat_1 @ sk_F @ X0)))
% 0.48/0.71          | ~ (v1_relat_1 @ sk_F))),
% 0.48/0.71      inference('sup+', [status(thm)], ['97', '98'])).
% 0.48/0.71  thf(t172_relat_1, axiom,
% 0.48/0.71    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.71  thf('100', plain,
% 0.48/0.71      (![X11 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [t172_relat_1])).
% 0.48/0.71  thf('101', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.71  thf('102', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k10_relat_1 @ sk_F @ X0)))),
% 0.48/0.71      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.48/0.71  thf('103', plain,
% 0.48/0.71      (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k1_relat_1 @ sk_F)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['78', '102'])).
% 0.48/0.71  thf('104', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(cc5_funct_2, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.48/0.71       ( ![C:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.48/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.48/0.71  thf('105', plain,
% 0.48/0.71      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.48/0.71          | (v1_partfun1 @ X30 @ X31)
% 0.48/0.71          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.48/0.71          | ~ (v1_funct_1 @ X30)
% 0.48/0.71          | (v1_xboole_0 @ X32))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.48/0.71  thf('106', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_B)
% 0.48/0.71        | ~ (v1_funct_1 @ sk_F)
% 0.48/0.71        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.48/0.71        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['104', '105'])).
% 0.48/0.71  thf('107', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('108', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('109', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.48/0.71  thf('110', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('111', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.48/0.71      inference('clc', [status(thm)], ['109', '110'])).
% 0.48/0.71  thf(d4_partfun1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.48/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.48/0.71  thf('112', plain,
% 0.48/0.71      (![X33 : $i, X34 : $i]:
% 0.48/0.71         (~ (v1_partfun1 @ X34 @ X33)
% 0.48/0.71          | ((k1_relat_1 @ X34) = (X33))
% 0.48/0.71          | ~ (v4_relat_1 @ X34 @ X33)
% 0.48/0.71          | ~ (v1_relat_1 @ X34))),
% 0.48/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.48/0.71  thf('113', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ sk_F)
% 0.48/0.71        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.48/0.71        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['111', '112'])).
% 0.48/0.71  thf('114', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.71  thf('115', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.48/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.48/0.71  thf('116', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.48/0.71  thf('117', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['103', '116'])).
% 0.48/0.71  thf('118', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k2_partfun1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71     ( ( ( v1_funct_1 @ C ) & 
% 0.48/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.71       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.48/0.71  thf('119', plain,
% 0.48/0.71      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.48/0.71          | ~ (v1_funct_1 @ X35)
% 0.48/0.71          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.48/0.71  thf('120', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.48/0.71          | ~ (v1_funct_1 @ sk_E))),
% 0.48/0.71      inference('sup-', [status(thm)], ['118', '119'])).
% 0.48/0.71  thf('121', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('122', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['120', '121'])).
% 0.48/0.71  thf('123', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('124', plain,
% 0.48/0.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.71         ((v4_relat_1 @ X27 @ X28)
% 0.48/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.71  thf('125', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.48/0.71      inference('sup-', [status(thm)], ['123', '124'])).
% 0.48/0.71  thf('126', plain,
% 0.48/0.71      (![X15 : $i, X16 : $i]:
% 0.48/0.71         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.48/0.71          | ~ (v4_relat_1 @ X15 @ X16)
% 0.48/0.71          | ~ (v1_relat_1 @ X15))),
% 0.48/0.71      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.48/0.71  thf('127', plain,
% 0.48/0.71      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['125', '126'])).
% 0.48/0.71  thf('128', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('129', plain,
% 0.48/0.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.71         ((v1_relat_1 @ X24)
% 0.48/0.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.48/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.71  thf('130', plain, ((v1_relat_1 @ sk_E)),
% 0.48/0.71      inference('sup-', [status(thm)], ['128', '129'])).
% 0.48/0.71  thf('131', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C))),
% 0.48/0.71      inference('demod', [status(thm)], ['127', '130'])).
% 0.48/0.71  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.48/0.71  thf('132', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.48/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.71  thf('133', plain,
% 0.48/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.71         (~ (r1_xboole_0 @ X12 @ X13)
% 0.48/0.71          | ~ (v1_relat_1 @ X14)
% 0.48/0.71          | ((k7_relat_1 @ (k7_relat_1 @ X14 @ X12) @ X13) = (k1_xboole_0)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.48/0.71  thf('134', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.71          | ~ (v1_relat_1 @ X1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.71  thf('135', plain,
% 0.48/0.71      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.71        | ~ (v1_relat_1 @ sk_E))),
% 0.48/0.71      inference('sup+', [status(thm)], ['131', '134'])).
% 0.48/0.71  thf('136', plain, ((v1_relat_1 @ sk_E)),
% 0.48/0.71      inference('sup-', [status(thm)], ['128', '129'])).
% 0.48/0.71  thf('137', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['135', '136'])).
% 0.48/0.71  thf('138', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('139', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['103', '116'])).
% 0.48/0.71  thf('140', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('141', plain,
% 0.48/0.71      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.48/0.71          | ~ (v1_funct_1 @ X35)
% 0.48/0.71          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.48/0.71  thf('142', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.48/0.71          | ~ (v1_funct_1 @ sk_F))),
% 0.48/0.71      inference('sup-', [status(thm)], ['140', '141'])).
% 0.48/0.71  thf('143', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('144', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['142', '143'])).
% 0.48/0.71  thf('145', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['60', '63'])).
% 0.48/0.71  thf('146', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.71          | ~ (v1_relat_1 @ X1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['132', '133'])).
% 0.48/0.71  thf('147', plain,
% 0.48/0.71      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.71        | ~ (v1_relat_1 @ sk_F))),
% 0.48/0.71      inference('sup+', [status(thm)], ['145', '146'])).
% 0.48/0.71  thf('148', plain, ((v1_relat_1 @ sk_F)),
% 0.48/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.48/0.71  thf('149', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['147', '148'])).
% 0.48/0.71  thf('150', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('151', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('152', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('153', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('154', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71            = (sk_E))
% 0.48/0.71        | ~ (v1_funct_2 @ 
% 0.48/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_A))),
% 0.48/0.71      inference('demod', [status(thm)],
% 0.48/0.71                ['48', '49', '50', '51', '52', '55', '117', '122', '137', 
% 0.48/0.71                 '138', '139', '144', '149', '150', '151', '152', '153'])).
% 0.48/0.71  thf('155', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ~ (v1_funct_2 @ 
% 0.48/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71            = (sk_E))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify', [status(thm)], ['154'])).
% 0.48/0.71  thf('156', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71            = (sk_E))
% 0.48/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['30', '155'])).
% 0.48/0.71  thf('157', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71            = (sk_E))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify', [status(thm)], ['156'])).
% 0.48/0.71  thf('158', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71            != (sk_E))
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            != (sk_F)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('159', plain,
% 0.48/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71          != (sk_E)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71                = (sk_E))))),
% 0.48/0.71      inference('split', [status(esa)], ['158'])).
% 0.48/0.71  thf('160', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['142', '143'])).
% 0.48/0.71  thf('161', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['103', '116'])).
% 0.48/0.71  thf('162', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.48/0.71      inference('split', [status(esa)], ['158'])).
% 0.48/0.71  thf('163', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('164', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('165', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.48/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.48/0.71      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.48/0.71  thf('166', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.48/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['161', '165'])).
% 0.48/0.71  thf('167', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['103', '116'])).
% 0.48/0.71  thf('168', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.48/0.71          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.48/0.71      inference('demod', [status(thm)], ['166', '167'])).
% 0.48/0.71  thf('169', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.48/0.71          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['160', '168'])).
% 0.48/0.71  thf('170', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['120', '121'])).
% 0.48/0.71  thf('171', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['135', '136'])).
% 0.48/0.71  thf('172', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['147', '148'])).
% 0.48/0.71  thf('173', plain,
% 0.48/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.48/0.71      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 0.48/0.71  thf('174', plain,
% 0.48/0.71      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.48/0.71      inference('simplify', [status(thm)], ['173'])).
% 0.48/0.71  thf('175', plain,
% 0.48/0.71      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.71  thf('176', plain,
% 0.48/0.71      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.48/0.71  thf('177', plain,
% 0.48/0.71      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71         (k1_zfmisc_1 @ 
% 0.48/0.71          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['43', '44'])).
% 0.48/0.71  thf('178', plain,
% 0.48/0.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.48/0.71         ((v1_xboole_0 @ X39)
% 0.48/0.71          | (v1_xboole_0 @ X40)
% 0.48/0.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.48/0.71          | ~ (v1_funct_1 @ X42)
% 0.48/0.71          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.48/0.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.48/0.71          | ((X45) != (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42))
% 0.48/0.71          | ((k2_partfun1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39 @ X45 @ X40)
% 0.48/0.71              = (X42))
% 0.48/0.71          | ~ (m1_subset_1 @ X45 @ 
% 0.48/0.71               (k1_zfmisc_1 @ 
% 0.48/0.71                (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39)))
% 0.48/0.71          | ~ (v1_funct_2 @ X45 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39)
% 0.48/0.71          | ~ (v1_funct_1 @ X45)
% 0.48/0.71          | ((k2_partfun1 @ X44 @ X39 @ X43 @ (k9_subset_1 @ X41 @ X44 @ X40))
% 0.48/0.71              != (k2_partfun1 @ X40 @ X39 @ X42 @ 
% 0.48/0.71                  (k9_subset_1 @ X41 @ X44 @ X40)))
% 0.48/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X39)))
% 0.48/0.71          | ~ (v1_funct_2 @ X43 @ X44 @ X39)
% 0.48/0.71          | ~ (v1_funct_1 @ X43)
% 0.48/0.71          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X41))
% 0.48/0.71          | (v1_xboole_0 @ X44)
% 0.48/0.71          | (v1_xboole_0 @ X41))),
% 0.48/0.71      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.48/0.71  thf('179', plain,
% 0.48/0.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.71         ((v1_xboole_0 @ X41)
% 0.48/0.71          | (v1_xboole_0 @ X44)
% 0.48/0.71          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X41))
% 0.48/0.71          | ~ (v1_funct_1 @ X43)
% 0.48/0.71          | ~ (v1_funct_2 @ X43 @ X44 @ X39)
% 0.48/0.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X39)))
% 0.48/0.71          | ((k2_partfun1 @ X44 @ X39 @ X43 @ (k9_subset_1 @ X41 @ X44 @ X40))
% 0.48/0.71              != (k2_partfun1 @ X40 @ X39 @ X42 @ 
% 0.48/0.71                  (k9_subset_1 @ X41 @ X44 @ X40)))
% 0.48/0.71          | ~ (v1_funct_1 @ (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42))
% 0.48/0.71          | ~ (v1_funct_2 @ (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42) @ 
% 0.48/0.71               (k4_subset_1 @ X41 @ X44 @ X40) @ X39)
% 0.48/0.71          | ~ (m1_subset_1 @ (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42) @ 
% 0.48/0.71               (k1_zfmisc_1 @ 
% 0.48/0.71                (k2_zfmisc_1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39)))
% 0.48/0.71          | ((k2_partfun1 @ (k4_subset_1 @ X41 @ X44 @ X40) @ X39 @ 
% 0.48/0.71              (k1_tmap_1 @ X41 @ X39 @ X44 @ X40 @ X43 @ X42) @ X40) = (
% 0.48/0.71              X42))
% 0.48/0.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.48/0.71          | ~ (v1_funct_2 @ X42 @ X40 @ X39)
% 0.48/0.71          | ~ (v1_funct_1 @ X42)
% 0.48/0.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.48/0.71          | (v1_xboole_0 @ X40)
% 0.48/0.71          | (v1_xboole_0 @ X39))),
% 0.48/0.71      inference('simplify', [status(thm)], ['178'])).
% 0.48/0.71  thf('180', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.71        | ~ (v1_funct_1 @ sk_F)
% 0.48/0.71        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.48/0.71        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            = (sk_F))
% 0.48/0.71        | ~ (v1_funct_2 @ 
% 0.48/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.48/0.71            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.48/0.71        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.48/0.71        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.48/0.71        | ~ (v1_funct_1 @ sk_E)
% 0.48/0.71        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['177', '179'])).
% 0.48/0.71  thf('181', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('182', plain, ((v1_funct_1 @ sk_F)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('183', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('184', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('185', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('186', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['103', '116'])).
% 0.48/0.71  thf('187', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['120', '121'])).
% 0.48/0.71  thf('188', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['135', '136'])).
% 0.48/0.71  thf('189', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.48/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('190', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.48/0.71      inference('demod', [status(thm)], ['103', '116'])).
% 0.48/0.71  thf('191', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['142', '143'])).
% 0.48/0.71  thf('192', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['147', '148'])).
% 0.48/0.71  thf('193', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('194', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('195', plain, ((v1_funct_1 @ sk_E)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('196', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('197', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            = (sk_F))
% 0.48/0.71        | ~ (v1_funct_2 @ 
% 0.48/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_A))),
% 0.48/0.71      inference('demod', [status(thm)],
% 0.48/0.71                ['180', '181', '182', '183', '184', '185', '186', '187', 
% 0.48/0.71                 '188', '189', '190', '191', '192', '193', '194', '195', '196'])).
% 0.48/0.71  thf('198', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ~ (v1_funct_2 @ 
% 0.48/0.71             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.48/0.71             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            = (sk_F))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify', [status(thm)], ['197'])).
% 0.48/0.71  thf('199', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            = (sk_F))
% 0.48/0.71        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['176', '198'])).
% 0.48/0.71  thf('200', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            = (sk_F))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify', [status(thm)], ['199'])).
% 0.48/0.71  thf('201', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71            = (sk_F)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['175', '200'])).
% 0.48/0.71  thf('202', plain,
% 0.48/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71          = (sk_F))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify', [status(thm)], ['201'])).
% 0.48/0.71  thf('203', plain,
% 0.48/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71          != (sk_F)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71                = (sk_F))))),
% 0.48/0.71      inference('split', [status(esa)], ['158'])).
% 0.48/0.71  thf('204', plain,
% 0.48/0.71      (((((sk_F) != (sk_F))
% 0.48/0.71         | (v1_xboole_0 @ sk_D)
% 0.48/0.71         | (v1_xboole_0 @ sk_C)
% 0.48/0.71         | (v1_xboole_0 @ sk_B)
% 0.48/0.71         | (v1_xboole_0 @ sk_A)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71                = (sk_F))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['202', '203'])).
% 0.48/0.71  thf('205', plain,
% 0.48/0.71      ((((v1_xboole_0 @ sk_A)
% 0.48/0.71         | (v1_xboole_0 @ sk_B)
% 0.48/0.71         | (v1_xboole_0 @ sk_C)
% 0.48/0.71         | (v1_xboole_0 @ sk_D)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71                = (sk_F))))),
% 0.48/0.71      inference('simplify', [status(thm)], ['204'])).
% 0.48/0.71  thf('206', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('207', plain,
% 0.48/0.71      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71                = (sk_F))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['205', '206'])).
% 0.48/0.71  thf('208', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('209', plain,
% 0.48/0.71      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71                = (sk_F))))),
% 0.48/0.71      inference('clc', [status(thm)], ['207', '208'])).
% 0.48/0.71  thf('210', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('211', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_B))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71                = (sk_F))))),
% 0.48/0.71      inference('clc', [status(thm)], ['209', '210'])).
% 0.48/0.71  thf('212', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('213', plain,
% 0.48/0.71      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71          = (sk_F)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['211', '212'])).
% 0.48/0.71  thf('214', plain,
% 0.48/0.71      (~
% 0.48/0.71       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71          = (sk_E))) | 
% 0.48/0.71       ~
% 0.48/0.71       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.48/0.71          = (sk_F))) | 
% 0.48/0.71       ~
% 0.48/0.71       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.48/0.71          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.48/0.71             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.48/0.71      inference('split', [status(esa)], ['158'])).
% 0.48/0.71  thf('215', plain,
% 0.48/0.71      (~
% 0.48/0.71       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71          = (sk_E)))),
% 0.48/0.71      inference('sat_resolution*', [status(thm)], ['174', '213', '214'])).
% 0.48/0.71  thf('216', plain,
% 0.48/0.71      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.48/0.71         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.48/0.71         != (sk_E))),
% 0.48/0.71      inference('simpl_trail', [status(thm)], ['159', '215'])).
% 0.48/0.71  thf('217', plain,
% 0.48/0.71      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify_reflect-', [status(thm)], ['157', '216'])).
% 0.48/0.71  thf('218', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_D)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['15', '217'])).
% 0.48/0.71  thf('219', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_A)
% 0.48/0.71        | (v1_xboole_0 @ sk_B)
% 0.48/0.71        | (v1_xboole_0 @ sk_C)
% 0.48/0.71        | (v1_xboole_0 @ sk_D))),
% 0.48/0.71      inference('simplify', [status(thm)], ['218'])).
% 0.48/0.71  thf('220', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('221', plain,
% 0.48/0.71      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['219', '220'])).
% 0.48/0.71  thf('222', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('223', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.48/0.71      inference('clc', [status(thm)], ['221', '222'])).
% 0.48/0.71  thf('224', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('225', plain, ((v1_xboole_0 @ sk_B)),
% 0.48/0.71      inference('clc', [status(thm)], ['223', '224'])).
% 0.48/0.71  thf('226', plain, ($false), inference('demod', [status(thm)], ['0', '225'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.48/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
