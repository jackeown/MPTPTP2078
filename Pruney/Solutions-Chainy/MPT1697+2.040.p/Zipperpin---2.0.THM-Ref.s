%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YzfiahM3g0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:59 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 619 expanded)
%              Number of leaves         :   33 ( 191 expanded)
%              Depth                    :   40
%              Number of atoms          : 3678 (27500 expanded)
%              Number of equality atoms :  133 ( 891 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 )
      | ( ( k7_relat_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X31 @ X29 @ X28 @ X30 @ X27 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('9',plain,(
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
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
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
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X31 @ X29 @ X28 @ X30 @ X27 @ X32 ) @ ( k4_subset_1 @ X31 @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
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
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X31 ) )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X31 @ X29 @ X28 @ X30 @ X27 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X31 @ X28 @ X30 ) @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
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
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
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
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ( X26
       != ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 @ X26 @ X25 )
        = X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X25 @ X20 @ X24 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) )
       != ( k2_partfun1 @ X21 @ X20 @ X23 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X20 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X20 ) ) )
      | ( ( k2_partfun1 @ X25 @ X20 @ X24 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) )
       != ( k2_partfun1 @ X21 @ X20 @ X23 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) @ X25 )
        = X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
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
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['64','65'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k2_partfun1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k2_partfun1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','59','68','73','74','75','80','81','82','83','84'])).

thf('86',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
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
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','86'])).

thf('88',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('95',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('96',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('99',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('100',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('103',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['92','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('107',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['104','107'])).

thf('109',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['91','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('112',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('118',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('120',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ( X26
       != ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 @ X26 @ X21 )
        = X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_partfun1 @ X25 @ X20 @ X24 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) )
       != ( k2_partfun1 @ X21 @ X20 @ X23 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X20 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('121',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X20 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X20 ) ) )
      | ( ( k2_partfun1 @ X25 @ X20 @ X24 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) )
       != ( k2_partfun1 @ X21 @ X20 @ X23 @ ( k9_subset_1 @ X22 @ X25 @ X21 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X22 @ X25 @ X21 ) @ X20 @ ( k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23 ) @ X21 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
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
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

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
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128','129','130','131','132','133','134','135','136'])).

thf('138',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
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
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','138'])).

thf('140',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','140'])).

thf('142',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['116','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['105','106'])).

thf('145',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['115','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['110','111'])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['89'])).

thf('151',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('162',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['114','160','161'])).

thf('163',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['90','162'])).

thf('164',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['88','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','164'])).

thf('166',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['105','106'])).

thf('169',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['110','111'])).

thf('172',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['0','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YzfiahM3g0
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 143 iterations in 0.151s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.62  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.44/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(t6_tmap_1, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.62                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62               ( ![D:$i]:
% 0.44/0.62                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.62                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62                   ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.62                     ( ![E:$i]:
% 0.44/0.62                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.62                           ( m1_subset_1 @
% 0.44/0.62                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.62                         ( ![F:$i]:
% 0.44/0.62                           ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.62                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.62                               ( m1_subset_1 @
% 0.44/0.62                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.62                             ( ( ( k2_partfun1 @
% 0.44/0.62                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.62                                 ( k2_partfun1 @
% 0.44/0.62                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.62                               ( ( k2_partfun1 @
% 0.44/0.62                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.62                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.62                                 ( E ) ) & 
% 0.44/0.62                               ( ( k2_partfun1 @
% 0.44/0.62                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.62                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.62                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.62              ( ![C:$i]:
% 0.44/0.62                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.62                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62                  ( ![D:$i]:
% 0.44/0.62                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.62                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62                      ( ( r1_subset_1 @ C @ D ) =>
% 0.44/0.62                        ( ![E:$i]:
% 0.44/0.62                          ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.62                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.62                              ( m1_subset_1 @
% 0.44/0.62                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.62                            ( ![F:$i]:
% 0.44/0.62                              ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.62                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.62                                  ( m1_subset_1 @
% 0.44/0.62                                    F @ 
% 0.44/0.62                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.62                                ( ( ( k2_partfun1 @
% 0.44/0.62                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.62                                    ( k2_partfun1 @
% 0.44/0.62                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.44/0.62                                  ( ( k2_partfun1 @
% 0.44/0.62                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.62                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.44/0.62                                    ( E ) ) & 
% 0.44/0.62                                  ( ( k2_partfun1 @
% 0.44/0.62                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.44/0.62                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.44/0.62                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.44/0.62  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.44/0.62  thf('1', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.44/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.62  thf(t95_relat_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ B ) =>
% 0.44/0.62       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.62         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X9 : $i, X10 : $i]:
% 0.44/0.62         (~ (r1_xboole_0 @ (k1_relat_1 @ X9) @ X10)
% 0.44/0.62          | ((k7_relat_1 @ X9 @ X10) = (k1_xboole_0))
% 0.44/0.62          | ~ (v1_relat_1 @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('5', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(dt_k1_tmap_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.62         ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.62         ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.44/0.62         ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.44/0.62         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.62       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.62         ( v1_funct_2 @
% 0.44/0.62           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.62           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.62         ( m1_subset_1 @
% 0.44/0.62           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.44/0.62          | ~ (v1_funct_1 @ X27)
% 0.44/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.44/0.62          | (v1_xboole_0 @ X30)
% 0.44/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X31))
% 0.44/0.62          | (v1_xboole_0 @ X28)
% 0.44/0.62          | (v1_xboole_0 @ X29)
% 0.44/0.62          | (v1_xboole_0 @ X31)
% 0.44/0.62          | ~ (v1_funct_1 @ X32)
% 0.44/0.62          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 0.44/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.44/0.62          | (v1_funct_1 @ (k1_tmap_1 @ X31 @ X29 @ X28 @ X30 @ X27 @ X32)))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | (v1_xboole_0 @ X2)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.62          | (v1_xboole_0 @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.44/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.62          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('11', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.44/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | (v1_xboole_0 @ X2)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.44/0.62          | (v1_xboole_0 @ X1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.62      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_D)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.62          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.62          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['6', '12'])).
% 0.44/0.62  thf('14', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('15', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_D)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.44/0.62      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '16'])).
% 0.44/0.62  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.44/0.62          | ~ (v1_funct_1 @ X27)
% 0.44/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.44/0.62          | (v1_xboole_0 @ X30)
% 0.44/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X31))
% 0.44/0.62          | (v1_xboole_0 @ X28)
% 0.44/0.62          | (v1_xboole_0 @ X29)
% 0.44/0.62          | (v1_xboole_0 @ X31)
% 0.44/0.62          | ~ (v1_funct_1 @ X32)
% 0.44/0.62          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 0.44/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.44/0.62          | (v1_funct_2 @ (k1_tmap_1 @ X31 @ X29 @ X28 @ X30 @ X27 @ X32) @ 
% 0.44/0.62             (k4_subset_1 @ X31 @ X28 @ X30) @ X29))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.62           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.62          | ~ (v1_funct_1 @ X2)
% 0.44/0.62          | (v1_xboole_0 @ X1)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.62          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.62  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('26', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.62           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.44/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.62          | ~ (v1_funct_1 @ X2)
% 0.44/0.62          | (v1_xboole_0 @ X1)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_D)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.62          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.62          | (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['21', '27'])).
% 0.44/0.62  thf('29', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('30', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_D)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.44/0.62      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['20', '31'])).
% 0.44/0.62  thf('33', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.44/0.62  thf('35', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.44/0.62          | ~ (v1_funct_1 @ X27)
% 0.44/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.44/0.62          | (v1_xboole_0 @ X30)
% 0.44/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X31))
% 0.44/0.62          | (v1_xboole_0 @ X28)
% 0.44/0.62          | (v1_xboole_0 @ X29)
% 0.44/0.62          | (v1_xboole_0 @ X31)
% 0.44/0.62          | ~ (v1_funct_1 @ X32)
% 0.44/0.62          | ~ (v1_funct_2 @ X32 @ X30 @ X29)
% 0.44/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.44/0.62          | (m1_subset_1 @ (k1_tmap_1 @ X31 @ X29 @ X28 @ X30 @ X27 @ X32) @ 
% 0.44/0.62             (k1_zfmisc_1 @ 
% 0.44/0.62              (k2_zfmisc_1 @ (k4_subset_1 @ X31 @ X28 @ X30) @ X29))))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.62          | ~ (v1_funct_1 @ X2)
% 0.44/0.62          | (v1_xboole_0 @ X1)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.44/0.62          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.44/0.62  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('41', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.44/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.44/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.44/0.62          | ~ (v1_funct_1 @ X2)
% 0.44/0.62          | (v1_xboole_0 @ X1)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_D)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ sk_F)
% 0.44/0.62          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.62          | (m1_subset_1 @ 
% 0.44/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k1_zfmisc_1 @ 
% 0.44/0.62              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['36', '42'])).
% 0.44/0.62  thf('44', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('45', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_D)
% 0.44/0.62          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.44/0.62          | (v1_xboole_0 @ sk_C)
% 0.44/0.62          | (v1_xboole_0 @ sk_B)
% 0.44/0.62          | (v1_xboole_0 @ X0)
% 0.44/0.62          | (m1_subset_1 @ 
% 0.44/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k1_zfmisc_1 @ 
% 0.44/0.62              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.44/0.62      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k1_zfmisc_1 @ 
% 0.44/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['35', '46'])).
% 0.44/0.62  thf('48', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k1_zfmisc_1 @ 
% 0.44/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.44/0.62  thf(d1_tmap_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.44/0.62                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62               ( ![D:$i]:
% 0.44/0.62                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.44/0.62                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.62                   ( ![E:$i]:
% 0.44/0.62                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.44/0.62                         ( m1_subset_1 @
% 0.44/0.62                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.44/0.62                       ( ![F:$i]:
% 0.44/0.62                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.44/0.62                             ( m1_subset_1 @
% 0.44/0.62                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.44/0.62                           ( ( ( k2_partfun1 @
% 0.44/0.62                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.44/0.62                               ( k2_partfun1 @
% 0.44/0.62                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.44/0.62                             ( ![G:$i]:
% 0.44/0.62                               ( ( ( v1_funct_1 @ G ) & 
% 0.44/0.62                                   ( v1_funct_2 @
% 0.44/0.62                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.44/0.62                                   ( m1_subset_1 @
% 0.44/0.62                                     G @ 
% 0.44/0.62                                     ( k1_zfmisc_1 @
% 0.44/0.62                                       ( k2_zfmisc_1 @
% 0.44/0.62                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.44/0.62                                 ( ( ( G ) =
% 0.44/0.62                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.62                                   ( ( ( k2_partfun1 @
% 0.44/0.62                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.62                                         C ) =
% 0.44/0.62                                       ( E ) ) & 
% 0.44/0.62                                     ( ( k2_partfun1 @
% 0.44/0.62                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.44/0.62                                         D ) =
% 0.44/0.62                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X20)
% 0.44/0.62          | (v1_xboole_0 @ X21)
% 0.44/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | ~ (v1_funct_1 @ X23)
% 0.44/0.62          | ~ (v1_funct_2 @ X23 @ X21 @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.44/0.62          | ((X26) != (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23))
% 0.44/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20 @ X26 @ X25)
% 0.44/0.62              = (X24))
% 0.44/0.62          | ~ (m1_subset_1 @ X26 @ 
% 0.44/0.62               (k1_zfmisc_1 @ 
% 0.44/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20)))
% 0.44/0.62          | ~ (v1_funct_2 @ X26 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20)
% 0.44/0.62          | ~ (v1_funct_1 @ X26)
% 0.44/0.62          | ((k2_partfun1 @ X25 @ X20 @ X24 @ (k9_subset_1 @ X22 @ X25 @ X21))
% 0.44/0.62              != (k2_partfun1 @ X21 @ X20 @ X23 @ 
% 0.44/0.62                  (k9_subset_1 @ X22 @ X25 @ X21)))
% 0.44/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X20)))
% 0.44/0.62          | ~ (v1_funct_2 @ X24 @ X25 @ X20)
% 0.44/0.62          | ~ (v1_funct_1 @ X24)
% 0.44/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | (v1_xboole_0 @ X25)
% 0.44/0.62          | (v1_xboole_0 @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X22)
% 0.44/0.62          | (v1_xboole_0 @ X25)
% 0.44/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | ~ (v1_funct_1 @ X24)
% 0.44/0.62          | ~ (v1_funct_2 @ X24 @ X25 @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X20)))
% 0.44/0.62          | ((k2_partfun1 @ X25 @ X20 @ X24 @ (k9_subset_1 @ X22 @ X25 @ X21))
% 0.44/0.62              != (k2_partfun1 @ X21 @ X20 @ X23 @ 
% 0.44/0.62                  (k9_subset_1 @ X22 @ X25 @ X21)))
% 0.44/0.62          | ~ (v1_funct_1 @ (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23))
% 0.44/0.62          | ~ (v1_funct_2 @ (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23) @ 
% 0.44/0.62               (k4_subset_1 @ X22 @ X25 @ X21) @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23) @ 
% 0.44/0.62               (k1_zfmisc_1 @ 
% 0.44/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20)))
% 0.44/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20 @ 
% 0.44/0.62              (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23) @ X25) = (
% 0.44/0.62              X24))
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.44/0.62          | ~ (v1_funct_2 @ X23 @ X21 @ X20)
% 0.44/0.62          | ~ (v1_funct_1 @ X23)
% 0.44/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | (v1_xboole_0 @ X21)
% 0.44/0.62          | (v1_xboole_0 @ X20))),
% 0.44/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.44/0.62  thf('52', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.62        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62            = (sk_E))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.62        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.62        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['49', '51'])).
% 0.44/0.62  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('54', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('55', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('57', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.62         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.44/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.62  thf('59', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.62  thf('60', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_r1_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.44/0.62       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.44/0.62  thf('61', plain,
% 0.44/0.62      (![X11 : $i, X12 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X11)
% 0.44/0.62          | (v1_xboole_0 @ X12)
% 0.44/0.62          | (r1_xboole_0 @ X11 @ X12)
% 0.44/0.62          | ~ (r1_subset_1 @ X11 @ X12))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.44/0.62  thf('62', plain,
% 0.44/0.62      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('63', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('64', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.44/0.62      inference('clc', [status(thm)], ['62', '63'])).
% 0.44/0.62  thf('65', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('66', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.44/0.62      inference('clc', [status(thm)], ['64', '65'])).
% 0.44/0.62  thf(d7_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.62  thf('67', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.62  thf('68', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.62  thf('69', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k2_partfun1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.62     ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.62       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.44/0.62  thf('70', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.44/0.62          | ~ (v1_funct_1 @ X16)
% 0.44/0.62          | ((k2_partfun1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.62  thf('71', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.44/0.62          | ~ (v1_funct_1 @ sk_E))),
% 0.44/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.44/0.62  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('73', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.62  thf('74', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.62  thf('75', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.62  thf('76', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.44/0.62          | ~ (v1_funct_1 @ X16)
% 0.44/0.62          | ((k2_partfun1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.44/0.62          | ~ (v1_funct_1 @ sk_F))),
% 0.44/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.44/0.62  thf('79', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('80', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('81', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('82', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('84', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('85', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62            = (sk_E))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.44/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['52', '53', '54', '55', '56', '59', '68', '73', '74', '75', 
% 0.44/0.62                 '80', '81', '82', '83', '84'])).
% 0.44/0.62  thf('86', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62            = (sk_E))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['85'])).
% 0.44/0.62  thf('87', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62            = (sk_E))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.44/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '86'])).
% 0.44/0.62  thf('88', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62            = (sk_E))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['87'])).
% 0.44/0.62  thf('89', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62            != (sk_E))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            != (sk_F)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('90', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62          != (sk_E)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62                = (sk_E))))),
% 0.44/0.62      inference('split', [status(esa)], ['89'])).
% 0.44/0.62  thf('91', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('92', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('93', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('94', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.62  thf('95', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('split', [status(esa)], ['89'])).
% 0.44/0.62  thf('96', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.62  thf('97', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.62  thf('98', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.62  thf('99', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.62  thf('100', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.44/0.62  thf('101', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.44/0.62          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['93', '100'])).
% 0.44/0.62  thf('102', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.62  thf('103', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['101', '102'])).
% 0.44/0.62  thf('104', plain,
% 0.44/0.62      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62         | ~ (v1_relat_1 @ sk_F)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['92', '103'])).
% 0.44/0.62  thf('105', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(cc1_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( v1_relat_1 @ C ) ))).
% 0.44/0.62  thf('106', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.62         ((v1_relat_1 @ X13)
% 0.44/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.62  thf('107', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.62  thf('108', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['104', '107'])).
% 0.44/0.62  thf('109', plain,
% 0.44/0.62      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['91', '108'])).
% 0.44/0.62  thf('110', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('111', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.62         ((v1_relat_1 @ X13)
% 0.44/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.62  thf('112', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.62      inference('sup-', [status(thm)], ['110', '111'])).
% 0.44/0.62  thf('113', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['109', '112'])).
% 0.44/0.62  thf('114', plain,
% 0.44/0.62      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['113'])).
% 0.44/0.62  thf('115', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('116', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v1_relat_1 @ X0)
% 0.44/0.62          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('117', plain,
% 0.44/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('118', plain,
% 0.44/0.62      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.44/0.62  thf('119', plain,
% 0.44/0.62      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62         (k1_zfmisc_1 @ 
% 0.44/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.44/0.62  thf('120', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X20)
% 0.44/0.62          | (v1_xboole_0 @ X21)
% 0.44/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | ~ (v1_funct_1 @ X23)
% 0.44/0.62          | ~ (v1_funct_2 @ X23 @ X21 @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.44/0.62          | ((X26) != (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23))
% 0.44/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20 @ X26 @ X21)
% 0.44/0.62              = (X23))
% 0.44/0.62          | ~ (m1_subset_1 @ X26 @ 
% 0.44/0.62               (k1_zfmisc_1 @ 
% 0.44/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20)))
% 0.44/0.62          | ~ (v1_funct_2 @ X26 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20)
% 0.44/0.62          | ~ (v1_funct_1 @ X26)
% 0.44/0.62          | ((k2_partfun1 @ X25 @ X20 @ X24 @ (k9_subset_1 @ X22 @ X25 @ X21))
% 0.44/0.62              != (k2_partfun1 @ X21 @ X20 @ X23 @ 
% 0.44/0.62                  (k9_subset_1 @ X22 @ X25 @ X21)))
% 0.44/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X20)))
% 0.44/0.62          | ~ (v1_funct_2 @ X24 @ X25 @ X20)
% 0.44/0.62          | ~ (v1_funct_1 @ X24)
% 0.44/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | (v1_xboole_0 @ X25)
% 0.44/0.62          | (v1_xboole_0 @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.44/0.62  thf('121', plain,
% 0.44/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.62         ((v1_xboole_0 @ X22)
% 0.44/0.62          | (v1_xboole_0 @ X25)
% 0.44/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | ~ (v1_funct_1 @ X24)
% 0.44/0.62          | ~ (v1_funct_2 @ X24 @ X25 @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X20)))
% 0.44/0.62          | ((k2_partfun1 @ X25 @ X20 @ X24 @ (k9_subset_1 @ X22 @ X25 @ X21))
% 0.44/0.62              != (k2_partfun1 @ X21 @ X20 @ X23 @ 
% 0.44/0.62                  (k9_subset_1 @ X22 @ X25 @ X21)))
% 0.44/0.62          | ~ (v1_funct_1 @ (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23))
% 0.44/0.62          | ~ (v1_funct_2 @ (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23) @ 
% 0.44/0.62               (k4_subset_1 @ X22 @ X25 @ X21) @ X20)
% 0.44/0.62          | ~ (m1_subset_1 @ (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23) @ 
% 0.44/0.62               (k1_zfmisc_1 @ 
% 0.44/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20)))
% 0.44/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X22 @ X25 @ X21) @ X20 @ 
% 0.44/0.62              (k1_tmap_1 @ X22 @ X20 @ X25 @ X21 @ X24 @ X23) @ X21) = (
% 0.44/0.62              X23))
% 0.44/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.44/0.62          | ~ (v1_funct_2 @ X23 @ X21 @ X20)
% 0.44/0.62          | ~ (v1_funct_1 @ X23)
% 0.44/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.44/0.62          | (v1_xboole_0 @ X21)
% 0.44/0.62          | (v1_xboole_0 @ X20))),
% 0.44/0.62      inference('simplify', [status(thm)], ['120'])).
% 0.44/0.62  thf('122', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.44/0.62        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.44/0.62            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.44/0.62            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.44/0.62                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.44/0.62        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.44/0.62        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.44/0.62        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['119', '121'])).
% 0.44/0.62  thf('123', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('124', plain, ((v1_funct_1 @ sk_F)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('125', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('126', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('127', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.62  thf('128', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.62  thf('129', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.44/0.62  thf('130', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.62  thf('131', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.44/0.62  thf('132', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('133', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('134', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('135', plain, ((v1_funct_1 @ sk_E)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('136', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('137', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.44/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)],
% 0.44/0.62                ['122', '123', '124', '125', '126', '127', '128', '129', 
% 0.44/0.62                 '130', '131', '132', '133', '134', '135', '136'])).
% 0.44/0.62  thf('138', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ~ (v1_funct_2 @ 
% 0.44/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.44/0.62             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['137'])).
% 0.44/0.62  thf('139', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.44/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['118', '138'])).
% 0.44/0.62  thf('140', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['139'])).
% 0.44/0.62  thf('141', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.44/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['117', '140'])).
% 0.44/0.62  thf('142', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['141'])).
% 0.44/0.62  thf('143', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_F)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['116', '142'])).
% 0.44/0.62  thf('144', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.62  thf('145', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F)))),
% 0.44/0.62      inference('demod', [status(thm)], ['143', '144'])).
% 0.44/0.62  thf('146', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_E)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['115', '145'])).
% 0.44/0.62  thf('147', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.62      inference('sup-', [status(thm)], ['110', '111'])).
% 0.44/0.62  thf('148', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['146', '147'])).
% 0.44/0.62  thf('149', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62            = (sk_F)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['148'])).
% 0.44/0.62  thf('150', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          != (sk_F)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('split', [status(esa)], ['89'])).
% 0.44/0.62  thf('151', plain,
% 0.44/0.62      (((((sk_F) != (sk_F))
% 0.44/0.62         | (v1_xboole_0 @ sk_A)
% 0.44/0.62         | (v1_xboole_0 @ sk_B)
% 0.44/0.62         | (v1_xboole_0 @ sk_C)
% 0.44/0.62         | (v1_xboole_0 @ sk_D)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['149', '150'])).
% 0.44/0.62  thf('152', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_D)
% 0.44/0.62         | (v1_xboole_0 @ sk_C)
% 0.44/0.62         | (v1_xboole_0 @ sk_B)
% 0.44/0.62         | (v1_xboole_0 @ sk_A)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['151'])).
% 0.44/0.62  thf('153', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('154', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['152', '153'])).
% 0.44/0.62  thf('155', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('156', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B)))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('clc', [status(thm)], ['154', '155'])).
% 0.44/0.62  thf('157', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('158', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_B))
% 0.44/0.62         <= (~
% 0.44/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62                = (sk_F))))),
% 0.44/0.62      inference('clc', [status(thm)], ['156', '157'])).
% 0.44/0.62  thf('159', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('160', plain,
% 0.44/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.44/0.62          = (sk_F)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['158', '159'])).
% 0.44/0.62  thf('161', plain,
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
% 0.44/0.62      inference('split', [status(esa)], ['89'])).
% 0.44/0.62  thf('162', plain,
% 0.44/0.62      (~
% 0.44/0.62       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62          = (sk_E)))),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['114', '160', '161'])).
% 0.44/0.62  thf('163', plain,
% 0.44/0.62      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.44/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.44/0.62         != (sk_E))),
% 0.44/0.62      inference('simpl_trail', [status(thm)], ['90', '162'])).
% 0.44/0.62  thf('164', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['88', '163'])).
% 0.44/0.62  thf('165', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.44/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['19', '164'])).
% 0.44/0.62  thf('166', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('simplify', [status(thm)], ['165'])).
% 0.44/0.62  thf('167', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_F)
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['4', '166'])).
% 0.44/0.62  thf('168', plain, ((v1_relat_1 @ sk_F)),
% 0.44/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.44/0.62  thf('169', plain,
% 0.44/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['167', '168'])).
% 0.44/0.62  thf('170', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_E)
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '169'])).
% 0.44/0.62  thf('171', plain, ((v1_relat_1 @ sk_E)),
% 0.44/0.62      inference('sup-', [status(thm)], ['110', '111'])).
% 0.44/0.62  thf('172', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | (v1_xboole_0 @ sk_A)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_D))),
% 0.44/0.62      inference('demod', [status(thm)], ['170', '171'])).
% 0.44/0.62  thf('173', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_D)
% 0.44/0.62        | (v1_xboole_0 @ sk_C)
% 0.44/0.62        | (v1_xboole_0 @ sk_B)
% 0.44/0.62        | (v1_xboole_0 @ sk_A))),
% 0.44/0.62      inference('simplify', [status(thm)], ['172'])).
% 0.44/0.62  thf('174', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('175', plain,
% 0.44/0.62      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['173', '174'])).
% 0.44/0.62  thf('176', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('177', plain, (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.44/0.62      inference('clc', [status(thm)], ['175', '176'])).
% 0.44/0.62  thf('178', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('179', plain, ((v1_xboole_0 @ sk_B)),
% 0.44/0.62      inference('clc', [status(thm)], ['177', '178'])).
% 0.44/0.62  thf('180', plain, ($false), inference('demod', [status(thm)], ['0', '179'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
