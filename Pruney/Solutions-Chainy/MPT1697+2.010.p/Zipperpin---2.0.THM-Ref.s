%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VYevsLn1yM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:54 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  316 (2588 expanded)
%              Number of leaves         :   47 ( 773 expanded)
%              Depth                    :   40
%              Number of atoms          : 4034 (95409 expanded)
%              Number of equality atoms :  160 (3115 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_xboole_0 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X49 )
      | ( v1_xboole_0 @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52 ) ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_xboole_0 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X49 )
      | ( v1_xboole_0 @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52 ) @ ( k4_subset_1 @ X51 @ X48 @ X50 ) @ X49 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_xboole_0 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X49 )
      | ( v1_xboole_0 @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X51 @ X48 @ X50 ) @ X49 ) ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( X46
       != ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 @ X46 @ X45 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 ) ) )
      | ~ ( v1_funct_2 @ X46 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 )
      | ~ ( v1_funct_1 @ X46 )
      | ( ( k2_partfun1 @ X45 @ X40 @ X44 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) )
       != ( k2_partfun1 @ X41 @ X40 @ X43 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X40 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X40 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X40 ) ) )
      | ( ( k2_partfun1 @ X45 @ X40 @ X44 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) )
       != ( k2_partfun1 @ X41 @ X40 @ X43 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) @ X45 )
        = X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X40 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( r1_subset_1 @ X23 @ X24 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 )
        = ( k7_relat_1 @ X36 @ X39 ) ) ) ),
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
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_partfun1 @ X31 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['76','77'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('79',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_partfun1 @ X35 @ X34 )
      | ( ( k1_relat_1 @ X35 )
        = X34 )
      | ~ ( v4_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('82',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['80','83','86'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('88',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k7_relat_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['81','82'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('95',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['93','94'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('96',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_partfun1 @ X31 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_partfun1 @ X35 @ X34 )
      | ( ( k1_relat_1 @ X35 )
        = X34 )
      | ~ ( v4_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('113',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['93','94'])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    r1_tarski @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['101','114'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('116',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) @ X16 )
        = ( k9_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_C )
        = ( k9_relat_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ sk_C )
      = ( k9_relat_1 @ sk_F @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['92','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['81','82'])).

thf('120',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ sk_C )
    = ( k9_relat_1 @ sk_F @ sk_C ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','91'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('122',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('123',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_F ) @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['81','82'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['80','83','86'])).

thf('126',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['80','83','86'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('129',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k9_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['81','82'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( ( k9_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k9_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['120','133'])).

thf('135',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('136',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('138',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('139',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['137','142'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('144',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('145',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('147',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['145','146'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('148',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('149',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['136','147','148'])).

thf('150',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_C ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('152',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k7_relat_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('158',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('159',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 )
        = ( k7_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k7_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['137','142'])).

thf('165',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('166',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( r1_tarski @ ( k1_relat_1 @ sk_F ) @ sk_D ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['81','82'])).

thf('169',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_F ) @ sk_D ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['80','83','86'])).

thf('171',plain,(
    r1_tarski @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) @ X16 )
        = ( k9_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_D ) @ sk_D )
        = ( k9_relat_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ sk_D )
      = ( k9_relat_1 @ sk_E @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['164','173'])).

thf('175',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('177',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k9_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( ( k9_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k9_relat_1 @ sk_E @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('183',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['174','181','182'])).

thf('184',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('185',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['145','146'])).

thf('187',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('188',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_D ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('191',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','156','157','158','163','191','192','193','194','195'])).

thf('197',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
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
    inference('sup-',[status(thm)],['30','197'])).

thf('199',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('204',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['200'])).

thf('205',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('207',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('208',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('209',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['202','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('212',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','155'])).

thf('213',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['189','190'])).

thf('214',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('217',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('218',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('219',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( X46
       != ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 @ X46 @ X41 )
        = X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 ) ) )
      | ~ ( v1_funct_2 @ X46 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 )
      | ~ ( v1_funct_1 @ X46 )
      | ( ( k2_partfun1 @ X45 @ X40 @ X44 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) )
       != ( k2_partfun1 @ X41 @ X40 @ X43 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X40 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('220',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X40 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X40 ) ) )
      | ( ( k2_partfun1 @ X45 @ X40 @ X44 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) )
       != ( k2_partfun1 @ X41 @ X40 @ X43 @ ( k9_subset_1 @ X42 @ X45 @ X41 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X42 @ X45 @ X41 ) @ X40 @ ( k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43 ) @ X41 )
        = X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
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
    inference('sup-',[status(thm)],['218','220'])).

thf('222',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('227',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('229',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','155'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('231',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('233',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['189','190'])).

thf('234',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
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
    inference(demod,[status(thm)],['221','222','223','224','225','226','227','228','229','230','231','232','233','234','235','236','237'])).

thf('239',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,
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
    inference('sup-',[status(thm)],['217','239'])).

thf('241',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
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
    inference('sup-',[status(thm)],['216','241'])).

thf('243',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['200'])).

thf('245',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['200'])).

thf('256',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['215','254','255'])).

thf('257',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['201','256'])).

thf('258',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['199','257'])).

thf('259',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','258'])).

thf('260',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['264','265'])).

thf('267',plain,(
    $false ),
    inference(demod,[status(thm)],['0','266'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VYevsLn1yM
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 267 iterations in 0.207s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.67  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.47/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.47/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.67  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.67  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.47/0.67  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(t6_tmap_1, conjecture,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.67       ( ![B:$i]:
% 0.47/0.67         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.67           ( ![C:$i]:
% 0.47/0.67             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.67                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.67               ( ![D:$i]:
% 0.47/0.67                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.47/0.67                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.67                   ( ( r1_subset_1 @ C @ D ) =>
% 0.47/0.67                     ( ![E:$i]:
% 0.47/0.67                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.47/0.67                           ( m1_subset_1 @
% 0.47/0.67                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.47/0.67                         ( ![F:$i]:
% 0.47/0.67                           ( ( ( v1_funct_1 @ F ) & 
% 0.47/0.67                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.47/0.67                               ( m1_subset_1 @
% 0.47/0.67                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.47/0.67                             ( ( ( k2_partfun1 @
% 0.47/0.67                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.47/0.67                                 ( k2_partfun1 @
% 0.47/0.67                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.47/0.67                               ( ( k2_partfun1 @
% 0.47/0.67                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.47/0.67                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.47/0.68                                 ( E ) ) & 
% 0.47/0.68                               ( ( k2_partfun1 @
% 0.47/0.68                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.47/0.68                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.47/0.68                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i]:
% 0.47/0.68        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.68          ( ![B:$i]:
% 0.47/0.68            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68              ( ![C:$i]:
% 0.47/0.68                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.68                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.68                  ( ![D:$i]:
% 0.47/0.68                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.47/0.68                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.68                      ( ( r1_subset_1 @ C @ D ) =>
% 0.47/0.68                        ( ![E:$i]:
% 0.47/0.68                          ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.68                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.47/0.68                              ( m1_subset_1 @
% 0.47/0.68                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.47/0.68                            ( ![F:$i]:
% 0.47/0.68                              ( ( ( v1_funct_1 @ F ) & 
% 0.47/0.68                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.47/0.68                                  ( m1_subset_1 @
% 0.47/0.68                                    F @ 
% 0.47/0.68                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.47/0.68                                ( ( ( k2_partfun1 @
% 0.47/0.68                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.47/0.68                                    ( k2_partfun1 @
% 0.47/0.68                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.47/0.68                                  ( ( k2_partfun1 @
% 0.47/0.68                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.47/0.68                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.47/0.68                                    ( E ) ) & 
% 0.47/0.68                                  ( ( k2_partfun1 @
% 0.47/0.68                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.47/0.68                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.47/0.68                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.47/0.68  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(dt_k1_tmap_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.68         ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.47/0.68         ( ~( v1_xboole_0 @ D ) ) & 
% 0.47/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.47/0.68         ( v1_funct_2 @ E @ C @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.47/0.68         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.47/0.68       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.47/0.68         ( v1_funct_2 @
% 0.47/0.68           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.47/0.68           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.47/0.68         ( m1_subset_1 @
% 0.47/0.68           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.47/0.68           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.47/0.68          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.47/0.68          | ~ (v1_funct_1 @ X47)
% 0.47/0.68          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.47/0.68          | (v1_xboole_0 @ X50)
% 0.47/0.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X51))
% 0.47/0.68          | (v1_xboole_0 @ X48)
% 0.47/0.68          | (v1_xboole_0 @ X49)
% 0.47/0.68          | (v1_xboole_0 @ X51)
% 0.47/0.68          | ~ (v1_funct_1 @ X52)
% 0.47/0.68          | ~ (v1_funct_2 @ X52 @ X50 @ X49)
% 0.47/0.68          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.47/0.68          | (v1_funct_1 @ (k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52)))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.47/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.47/0.68          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | (v1_xboole_0 @ X2)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.47/0.68          | (v1_xboole_0 @ X1)
% 0.47/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.47/0.68          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.68  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.47/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.47/0.68          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | (v1_xboole_0 @ X2)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.47/0.68          | (v1_xboole_0 @ X1)
% 0.47/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.47/0.68      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_D)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.47/0.68          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['2', '8'])).
% 0.47/0.68  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_D)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.47/0.68      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['1', '12'])).
% 0.47/0.68  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.68  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.47/0.68          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.47/0.68          | ~ (v1_funct_1 @ X47)
% 0.47/0.68          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.47/0.68          | (v1_xboole_0 @ X50)
% 0.47/0.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X51))
% 0.47/0.68          | (v1_xboole_0 @ X48)
% 0.47/0.68          | (v1_xboole_0 @ X49)
% 0.47/0.68          | (v1_xboole_0 @ X51)
% 0.47/0.68          | ~ (v1_funct_1 @ X52)
% 0.47/0.68          | ~ (v1_funct_2 @ X52 @ X50 @ X49)
% 0.47/0.68          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.47/0.68          | (v1_funct_2 @ (k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52) @ 
% 0.47/0.68             (k4_subset_1 @ X51 @ X48 @ X50) @ X49))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.47/0.68           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.47/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.47/0.68          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.47/0.68          | ~ (v1_funct_1 @ X2)
% 0.47/0.68          | (v1_xboole_0 @ X1)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.47/0.68          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.68  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.47/0.68           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.47/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.47/0.68          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.47/0.68          | ~ (v1_funct_1 @ X2)
% 0.47/0.68          | (v1_xboole_0 @ X1)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.47/0.68      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_D)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.47/0.68          | (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['17', '23'])).
% 0.47/0.68  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_D)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '27'])).
% 0.47/0.68  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('30', plain,
% 0.47/0.68      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.68  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('32', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('33', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.47/0.68          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.47/0.68          | ~ (v1_funct_1 @ X47)
% 0.47/0.68          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.47/0.68          | (v1_xboole_0 @ X50)
% 0.47/0.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X51))
% 0.47/0.68          | (v1_xboole_0 @ X48)
% 0.47/0.68          | (v1_xboole_0 @ X49)
% 0.47/0.68          | (v1_xboole_0 @ X51)
% 0.47/0.68          | ~ (v1_funct_1 @ X52)
% 0.47/0.68          | ~ (v1_funct_2 @ X52 @ X50 @ X49)
% 0.47/0.68          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.47/0.68          | (m1_subset_1 @ (k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52) @ 
% 0.47/0.68             (k1_zfmisc_1 @ 
% 0.47/0.68              (k2_zfmisc_1 @ (k4_subset_1 @ X51 @ X48 @ X50) @ X49))))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.47/0.68  thf('35', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.47/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.47/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.47/0.68          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.47/0.68          | ~ (v1_funct_1 @ X2)
% 0.47/0.68          | (v1_xboole_0 @ X1)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.47/0.68          | ~ (v1_funct_1 @ sk_E)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.68         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.47/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.47/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.47/0.68          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.47/0.68          | ~ (v1_funct_1 @ X2)
% 0.47/0.68          | (v1_xboole_0 @ X1)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.47/0.68      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_D)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_F)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.47/0.68          | (m1_subset_1 @ 
% 0.47/0.68             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k1_zfmisc_1 @ 
% 0.47/0.68              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['32', '38'])).
% 0.47/0.68  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('42', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_D)
% 0.47/0.68          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.47/0.68          | (v1_xboole_0 @ sk_C)
% 0.47/0.68          | (v1_xboole_0 @ sk_B)
% 0.47/0.68          | (v1_xboole_0 @ X0)
% 0.47/0.68          | (m1_subset_1 @ 
% 0.47/0.68             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k1_zfmisc_1 @ 
% 0.47/0.68              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68         (k1_zfmisc_1 @ 
% 0.47/0.68          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['31', '42'])).
% 0.47/0.68  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68         (k1_zfmisc_1 @ 
% 0.47/0.68          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.47/0.68  thf(d1_tmap_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68           ( ![C:$i]:
% 0.47/0.68             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.68                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.68               ( ![D:$i]:
% 0.47/0.68                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.47/0.68                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.68                   ( ![E:$i]:
% 0.47/0.68                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.47/0.68                         ( m1_subset_1 @
% 0.47/0.68                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.47/0.68                       ( ![F:$i]:
% 0.47/0.68                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.47/0.68                             ( m1_subset_1 @
% 0.47/0.68                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.47/0.68                           ( ( ( k2_partfun1 @
% 0.47/0.68                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.47/0.68                               ( k2_partfun1 @
% 0.47/0.68                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.47/0.68                             ( ![G:$i]:
% 0.47/0.68                               ( ( ( v1_funct_1 @ G ) & 
% 0.47/0.68                                   ( v1_funct_2 @
% 0.47/0.68                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.47/0.68                                   ( m1_subset_1 @
% 0.47/0.68                                     G @ 
% 0.47/0.68                                     ( k1_zfmisc_1 @
% 0.47/0.68                                       ( k2_zfmisc_1 @
% 0.47/0.68                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.47/0.68                                 ( ( ( G ) =
% 0.47/0.68                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.47/0.68                                   ( ( ( k2_partfun1 @
% 0.47/0.68                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.47/0.68                                         C ) =
% 0.47/0.68                                       ( E ) ) & 
% 0.47/0.68                                     ( ( k2_partfun1 @
% 0.47/0.68                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.47/0.68                                         D ) =
% 0.47/0.68                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ X40)
% 0.47/0.68          | (v1_xboole_0 @ X41)
% 0.47/0.68          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | ~ (v1_funct_1 @ X43)
% 0.47/0.68          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.47/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.47/0.68          | ((X46) != (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.47/0.68          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ X46 @ X45)
% 0.47/0.68              = (X44))
% 0.47/0.68          | ~ (m1_subset_1 @ X46 @ 
% 0.47/0.68               (k1_zfmisc_1 @ 
% 0.47/0.68                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.47/0.68          | ~ (v1_funct_2 @ X46 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.47/0.68          | ~ (v1_funct_1 @ X46)
% 0.47/0.68          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.47/0.68              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.47/0.68                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.47/0.68          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.47/0.68          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.47/0.68          | ~ (v1_funct_1 @ X44)
% 0.47/0.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | (v1_xboole_0 @ X45)
% 0.47/0.68          | (v1_xboole_0 @ X42))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ X42)
% 0.47/0.68          | (v1_xboole_0 @ X45)
% 0.47/0.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | ~ (v1_funct_1 @ X44)
% 0.47/0.68          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.47/0.68          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.47/0.68          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.47/0.68              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.47/0.68                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.47/0.68          | ~ (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.47/0.68          | ~ (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.47/0.68               (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.47/0.68          | ~ (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.47/0.68               (k1_zfmisc_1 @ 
% 0.47/0.68                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.47/0.68          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ 
% 0.47/0.68              (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ X45) = (
% 0.47/0.68              X44))
% 0.47/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.47/0.68          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.47/0.68          | ~ (v1_funct_1 @ X43)
% 0.47/0.68          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | (v1_xboole_0 @ X41)
% 0.47/0.68          | (v1_xboole_0 @ X40))),
% 0.47/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | ~ (v1_funct_1 @ sk_F)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68            = (sk_E))
% 0.47/0.68        | ~ (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.47/0.68        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.47/0.68        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_E)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['45', '47'])).
% 0.47/0.68  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('52', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k9_subset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.47/0.68  thf('54', plain,
% 0.47/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.68         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 0.47/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.47/0.68  thf('55', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_r1_subset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.47/0.68       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.47/0.68  thf('57', plain,
% 0.47/0.68      (![X23 : $i, X24 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ X23)
% 0.47/0.68          | (v1_xboole_0 @ X24)
% 0.47/0.68          | (r1_xboole_0 @ X23 @ X24)
% 0.47/0.68          | ~ (r1_subset_1 @ X23 @ X24))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.47/0.68  thf('58', plain,
% 0.47/0.68      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.68  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.47/0.68      inference('clc', [status(thm)], ['58', '59'])).
% 0.47/0.68  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.47/0.68      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.68  thf(d7_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.68       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.68  thf('63', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.68  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('65', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k2_partfun1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.47/0.68  thf('66', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.47/0.68          | ~ (v1_funct_1 @ X36)
% 0.47/0.68          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.47/0.68  thf('67', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ sk_E))),
% 0.47/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.68  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('69', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.68  thf('70', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.47/0.68      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.68  thf('71', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc5_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68       ( ![C:$i]:
% 0.47/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.68             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('72', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.47/0.68          | (v1_partfun1 @ X31 @ X32)
% 0.47/0.68          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.47/0.68          | ~ (v1_funct_1 @ X31)
% 0.47/0.68          | (v1_xboole_0 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.68  thf('73', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_F)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.47/0.68        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.68  thf('74', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('75', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('76', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.47/0.68  thf('77', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('78', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.47/0.68      inference('clc', [status(thm)], ['76', '77'])).
% 0.47/0.68  thf(d4_partfun1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.68       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.68  thf('79', plain,
% 0.47/0.68      (![X34 : $i, X35 : $i]:
% 0.47/0.68         (~ (v1_partfun1 @ X35 @ X34)
% 0.47/0.68          | ((k1_relat_1 @ X35) = (X34))
% 0.47/0.68          | ~ (v4_relat_1 @ X35 @ X34)
% 0.47/0.68          | ~ (v1_relat_1 @ X35))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.68  thf('80', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_F)
% 0.47/0.68        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.47/0.68        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.47/0.68  thf('81', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc1_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( v1_relat_1 @ C ) ))).
% 0.47/0.68  thf('82', plain,
% 0.47/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.68         ((v1_relat_1 @ X25)
% 0.47/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.68  thf('83', plain, ((v1_relat_1 @ sk_F)),
% 0.47/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('84', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.68  thf('85', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X28 @ X29)
% 0.47/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('86', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.47/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.68  thf('87', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['80', '83', '86'])).
% 0.47/0.68  thf(t187_relat_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.47/0.68           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.47/0.68  thf('88', plain,
% 0.47/0.68      (![X19 : $i, X20 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X19 @ (k1_relat_1 @ X20))
% 0.47/0.68          | ((k7_relat_1 @ X20 @ X19) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X20))),
% 0.47/0.68      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.47/0.68  thf('89', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.47/0.68          | ~ (v1_relat_1 @ sk_F)
% 0.47/0.68          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.68  thf('90', plain, ((v1_relat_1 @ sk_F)),
% 0.47/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('91', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.47/0.68          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['89', '90'])).
% 0.47/0.68  thf('92', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['70', '91'])).
% 0.47/0.68  thf('93', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('94', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X28 @ X29)
% 0.47/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('95', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.68  thf(d18_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('96', plain,
% 0.47/0.68      (![X10 : $i, X11 : $i]:
% 0.47/0.68         (~ (v4_relat_1 @ X10 @ X11)
% 0.47/0.68          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.47/0.68          | ~ (v1_relat_1 @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.68  thf('97', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k1_relat_1 @ sk_E) @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.68  thf('98', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('99', plain,
% 0.47/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.68         ((v1_relat_1 @ X25)
% 0.47/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.68  thf('100', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('101', plain, ((r1_tarski @ (k1_relat_1 @ sk_E) @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['97', '100'])).
% 0.47/0.68  thf('102', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('103', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.47/0.68          | (v1_partfun1 @ X31 @ X32)
% 0.47/0.68          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.47/0.68          | ~ (v1_funct_1 @ X31)
% 0.47/0.68          | (v1_xboole_0 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.68  thf('104', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_E)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.47/0.68        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['102', '103'])).
% 0.47/0.68  thf('105', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('106', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('107', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.47/0.68  thf('108', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('109', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.47/0.68      inference('clc', [status(thm)], ['107', '108'])).
% 0.47/0.68  thf('110', plain,
% 0.47/0.68      (![X34 : $i, X35 : $i]:
% 0.47/0.68         (~ (v1_partfun1 @ X35 @ X34)
% 0.47/0.68          | ((k1_relat_1 @ X35) = (X34))
% 0.47/0.68          | ~ (v4_relat_1 @ X35 @ X34)
% 0.47/0.68          | ~ (v1_relat_1 @ X35))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.68  thf('111', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_E)
% 0.47/0.68        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.47/0.68        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['109', '110'])).
% 0.47/0.68  thf('112', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('113', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.68  thf('114', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.47/0.68  thf('115', plain, ((r1_tarski @ sk_C @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['101', '114'])).
% 0.47/0.68  thf(t162_relat_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) =>
% 0.47/0.68       ( ![B:$i,C:$i]:
% 0.47/0.68         ( ( r1_tarski @ B @ C ) =>
% 0.47/0.68           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.47/0.68             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.47/0.68  thf('116', plain,
% 0.47/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.68         (~ (r1_tarski @ X16 @ X17)
% 0.47/0.68          | ((k9_relat_1 @ (k7_relat_1 @ X18 @ X17) @ X16)
% 0.47/0.68              = (k9_relat_1 @ X18 @ X16))
% 0.47/0.68          | ~ (v1_relat_1 @ X18))),
% 0.47/0.68      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.47/0.68  thf('117', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_C)
% 0.47/0.68              = (k9_relat_1 @ X0 @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['115', '116'])).
% 0.47/0.68  thf('118', plain,
% 0.47/0.68      ((((k9_relat_1 @ k1_xboole_0 @ sk_C) = (k9_relat_1 @ sk_F @ sk_C))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_F))),
% 0.47/0.68      inference('sup+', [status(thm)], ['92', '117'])).
% 0.47/0.68  thf('119', plain, ((v1_relat_1 @ sk_F)),
% 0.47/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('120', plain,
% 0.47/0.68      (((k9_relat_1 @ k1_xboole_0 @ sk_C) = (k9_relat_1 @ sk_F @ sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['118', '119'])).
% 0.47/0.68  thf('121', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['70', '91'])).
% 0.47/0.68  thf(t95_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.68         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('122', plain,
% 0.47/0.68      (![X21 : $i, X22 : $i]:
% 0.47/0.68         (((k7_relat_1 @ X21 @ X22) != (k1_xboole_0))
% 0.47/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.47/0.68          | ~ (v1_relat_1 @ X21))),
% 0.47/0.68      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.47/0.68  thf('123', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_F)
% 0.47/0.68        | (r1_xboole_0 @ (k1_relat_1 @ sk_F) @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['121', '122'])).
% 0.47/0.68  thf('124', plain, ((v1_relat_1 @ sk_F)),
% 0.47/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('125', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['80', '83', '86'])).
% 0.47/0.68  thf('126', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_D @ sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.47/0.68  thf('127', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.47/0.68      inference('simplify', [status(thm)], ['126'])).
% 0.47/0.68  thf('128', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['80', '83', '86'])).
% 0.47/0.68  thf(t151_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.68         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('129', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.47/0.68          | ((k9_relat_1 @ X14 @ X15) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X14))),
% 0.47/0.68      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.47/0.68  thf('130', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ sk_F)
% 0.47/0.68          | ((k9_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['128', '129'])).
% 0.47/0.68  thf('131', plain, ((v1_relat_1 @ sk_F)),
% 0.47/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('132', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.47/0.68          | ((k9_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['130', '131'])).
% 0.47/0.68  thf('133', plain, (((k9_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['127', '132'])).
% 0.47/0.68  thf('134', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['120', '133'])).
% 0.47/0.68  thf('135', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (((k9_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 0.47/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.47/0.68          | ~ (v1_relat_1 @ X14))),
% 0.47/0.68      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.47/0.68  thf('136', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.68        | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['134', '135'])).
% 0.47/0.68  thf('137', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.47/0.68      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.68  thf('138', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.47/0.68  thf('139', plain,
% 0.47/0.68      (![X21 : $i, X22 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.47/0.68          | ((k7_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X21))),
% 0.47/0.68      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.47/0.68  thf('140', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ sk_C @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ sk_E)
% 0.47/0.68          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['138', '139'])).
% 0.47/0.68  thf('141', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('142', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ sk_C @ X0)
% 0.47/0.68          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['140', '141'])).
% 0.47/0.68  thf('143', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['137', '142'])).
% 0.47/0.68  thf(dt_k7_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.47/0.68  thf('144', plain,
% 0.47/0.68      (![X12 : $i, X13 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.47/0.68  thf('145', plain, (((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_E))),
% 0.47/0.68      inference('sup+', [status(thm)], ['143', '144'])).
% 0.47/0.68  thf('146', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('147', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.68      inference('demod', [status(thm)], ['145', '146'])).
% 0.47/0.68  thf(t60_relat_1, axiom,
% 0.47/0.68    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.68     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.68  thf('148', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.68  thf('149', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['136', '147', '148'])).
% 0.47/0.68  thf('150', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_C)),
% 0.47/0.68      inference('simplify', [status(thm)], ['149'])).
% 0.47/0.68  thf('151', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.47/0.68  thf('152', plain,
% 0.47/0.68      (![X19 : $i, X20 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X19 @ (k1_relat_1 @ X20))
% 0.47/0.68          | ((k7_relat_1 @ X20 @ X19) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X20))),
% 0.47/0.68      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.47/0.68  thf('153', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.47/0.68          | ~ (v1_relat_1 @ sk_E)
% 0.47/0.68          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['151', '152'])).
% 0.47/0.68  thf('154', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('155', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X0 @ sk_C)
% 0.47/0.68          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['153', '154'])).
% 0.47/0.68  thf('156', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['150', '155'])).
% 0.47/0.68  thf('157', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('158', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('159', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('160', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.47/0.68          | ~ (v1_funct_1 @ X36)
% 0.47/0.68          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.47/0.68  thf('161', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ sk_F))),
% 0.47/0.68      inference('sup-', [status(thm)], ['159', '160'])).
% 0.47/0.68  thf('162', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('163', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['161', '162'])).
% 0.47/0.68  thf('164', plain, (((k7_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['137', '142'])).
% 0.47/0.68  thf('165', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.47/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.68  thf('166', plain,
% 0.47/0.68      (![X10 : $i, X11 : $i]:
% 0.47/0.68         (~ (v4_relat_1 @ X10 @ X11)
% 0.47/0.68          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.47/0.68          | ~ (v1_relat_1 @ X10))),
% 0.47/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.68  thf('167', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_F) | (r1_tarski @ (k1_relat_1 @ sk_F) @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['165', '166'])).
% 0.47/0.68  thf('168', plain, ((v1_relat_1 @ sk_F)),
% 0.47/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('169', plain, ((r1_tarski @ (k1_relat_1 @ sk_F) @ sk_D)),
% 0.47/0.68      inference('demod', [status(thm)], ['167', '168'])).
% 0.47/0.68  thf('170', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['80', '83', '86'])).
% 0.47/0.68  thf('171', plain, ((r1_tarski @ sk_D @ sk_D)),
% 0.47/0.68      inference('demod', [status(thm)], ['169', '170'])).
% 0.47/0.68  thf('172', plain,
% 0.47/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.68         (~ (r1_tarski @ X16 @ X17)
% 0.47/0.68          | ((k9_relat_1 @ (k7_relat_1 @ X18 @ X17) @ X16)
% 0.47/0.68              = (k9_relat_1 @ X18 @ X16))
% 0.47/0.68          | ~ (v1_relat_1 @ X18))),
% 0.47/0.68      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.47/0.68  thf('173', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_D) @ sk_D)
% 0.47/0.68              = (k9_relat_1 @ X0 @ sk_D)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['171', '172'])).
% 0.47/0.68  thf('174', plain,
% 0.47/0.68      ((((k9_relat_1 @ k1_xboole_0 @ sk_D) = (k9_relat_1 @ sk_E @ sk_D))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_E))),
% 0.47/0.68      inference('sup+', [status(thm)], ['164', '173'])).
% 0.47/0.68  thf('175', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.47/0.68      inference('clc', [status(thm)], ['60', '61'])).
% 0.47/0.68  thf('176', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.47/0.68  thf('177', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.47/0.68          | ((k9_relat_1 @ X14 @ X15) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X14))),
% 0.47/0.68      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.47/0.68  thf('178', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ sk_C @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ sk_E)
% 0.47/0.68          | ((k9_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['176', '177'])).
% 0.47/0.68  thf('179', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('180', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ sk_C @ X0)
% 0.47/0.68          | ((k9_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['178', '179'])).
% 0.47/0.68  thf('181', plain, (((k9_relat_1 @ sk_E @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['175', '180'])).
% 0.47/0.68  thf('182', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('183', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['174', '181', '182'])).
% 0.47/0.68  thf('184', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (((k9_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 0.47/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.47/0.68          | ~ (v1_relat_1 @ X14))),
% 0.47/0.68      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.47/0.68  thf('185', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.68        | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['183', '184'])).
% 0.47/0.68  thf('186', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.68      inference('demod', [status(thm)], ['145', '146'])).
% 0.47/0.68  thf('187', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.68  thf('188', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.47/0.68  thf('189', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_D)),
% 0.47/0.68      inference('simplify', [status(thm)], ['188'])).
% 0.47/0.68  thf('190', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_xboole_0 @ X0 @ sk_D)
% 0.47/0.68          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['89', '90'])).
% 0.47/0.68  thf('191', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['189', '190'])).
% 0.47/0.68  thf('192', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('193', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('194', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('195', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('196', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68            = (sk_E))
% 0.47/0.68        | ~ (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)],
% 0.47/0.68                ['48', '49', '50', '51', '52', '55', '64', '69', '156', '157', 
% 0.47/0.68                 '158', '163', '191', '192', '193', '194', '195'])).
% 0.47/0.68  thf('197', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ~ (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68            = (sk_E))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify', [status(thm)], ['196'])).
% 0.47/0.68  thf('198', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68            = (sk_E))
% 0.47/0.68        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['30', '197'])).
% 0.47/0.68  thf('199', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68            = (sk_E))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify', [status(thm)], ['198'])).
% 0.47/0.68  thf('200', plain,
% 0.47/0.68      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68            != (sk_E))
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            != (sk_F)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('201', plain,
% 0.47/0.68      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68          != (sk_E)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68                = (sk_E))))),
% 0.47/0.68      inference('split', [status(esa)], ['200'])).
% 0.47/0.68  thf('202', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['161', '162'])).
% 0.47/0.68  thf('203', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('204', plain,
% 0.47/0.68      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.47/0.68      inference('split', [status(esa)], ['200'])).
% 0.47/0.68  thf('205', plain,
% 0.47/0.68      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['203', '204'])).
% 0.47/0.68  thf('206', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('207', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('208', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('209', plain,
% 0.47/0.68      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.47/0.68          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.47/0.68      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 0.47/0.68  thf('210', plain,
% 0.47/0.68      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.47/0.68          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['202', '209'])).
% 0.47/0.68  thf('211', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.68  thf('212', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['150', '155'])).
% 0.47/0.68  thf('213', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['189', '190'])).
% 0.47/0.68  thf('214', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.47/0.68      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 0.47/0.68  thf('215', plain,
% 0.47/0.68      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['214'])).
% 0.47/0.68  thf('216', plain,
% 0.47/0.68      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.68  thf('217', plain,
% 0.47/0.68      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.68  thf('218', plain,
% 0.47/0.68      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68         (k1_zfmisc_1 @ 
% 0.47/0.68          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.47/0.68  thf('219', plain,
% 0.47/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ X40)
% 0.47/0.68          | (v1_xboole_0 @ X41)
% 0.47/0.68          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | ~ (v1_funct_1 @ X43)
% 0.47/0.68          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.47/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.47/0.68          | ((X46) != (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.47/0.68          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ X46 @ X41)
% 0.47/0.68              = (X43))
% 0.47/0.68          | ~ (m1_subset_1 @ X46 @ 
% 0.47/0.68               (k1_zfmisc_1 @ 
% 0.47/0.68                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.47/0.68          | ~ (v1_funct_2 @ X46 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.47/0.68          | ~ (v1_funct_1 @ X46)
% 0.47/0.68          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.47/0.68              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.47/0.68                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.47/0.68          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.47/0.68          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.47/0.68          | ~ (v1_funct_1 @ X44)
% 0.47/0.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | (v1_xboole_0 @ X45)
% 0.47/0.68          | (v1_xboole_0 @ X42))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.47/0.68  thf('220', plain,
% 0.47/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ X42)
% 0.47/0.68          | (v1_xboole_0 @ X45)
% 0.47/0.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | ~ (v1_funct_1 @ X44)
% 0.47/0.68          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.47/0.68          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.47/0.68          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.47/0.68              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.47/0.68                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.47/0.68          | ~ (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.47/0.68          | ~ (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.47/0.68               (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.47/0.68          | ~ (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.47/0.68               (k1_zfmisc_1 @ 
% 0.47/0.68                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.47/0.68          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ 
% 0.47/0.68              (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ X41) = (
% 0.47/0.68              X43))
% 0.47/0.68          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.47/0.68          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.47/0.68          | ~ (v1_funct_1 @ X43)
% 0.47/0.68          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.47/0.68          | (v1_xboole_0 @ X41)
% 0.47/0.68          | (v1_xboole_0 @ X40))),
% 0.47/0.68      inference('simplify', [status(thm)], ['219'])).
% 0.47/0.68  thf('221', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | ~ (v1_funct_1 @ sk_F)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            = (sk_F))
% 0.47/0.68        | ~ (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.47/0.68            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.47/0.68        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.47/0.68        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_E)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['218', '220'])).
% 0.47/0.68  thf('222', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('223', plain, ((v1_funct_1 @ sk_F)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('224', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('225', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('226', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('227', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('228', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.68  thf('229', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['150', '155'])).
% 0.47/0.68  thf('230', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('231', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('232', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['161', '162'])).
% 0.47/0.68  thf('233', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['189', '190'])).
% 0.47/0.68  thf('234', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('235', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('236', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('237', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('238', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            = (sk_F))
% 0.47/0.68        | ~ (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_A))),
% 0.47/0.68      inference('demod', [status(thm)],
% 0.47/0.68                ['221', '222', '223', '224', '225', '226', '227', '228', 
% 0.47/0.68                 '229', '230', '231', '232', '233', '234', '235', '236', '237'])).
% 0.47/0.68  thf('239', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ~ (v1_funct_2 @ 
% 0.47/0.68             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.47/0.68             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            = (sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify', [status(thm)], ['238'])).
% 0.47/0.68  thf('240', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            = (sk_F))
% 0.47/0.68        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['217', '239'])).
% 0.47/0.68  thf('241', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            = (sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify', [status(thm)], ['240'])).
% 0.47/0.68  thf('242', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68            = (sk_F)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['216', '241'])).
% 0.47/0.68  thf('243', plain,
% 0.47/0.68      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68          = (sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify', [status(thm)], ['242'])).
% 0.47/0.68  thf('244', plain,
% 0.47/0.68      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68          != (sk_F)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68                = (sk_F))))),
% 0.47/0.68      inference('split', [status(esa)], ['200'])).
% 0.47/0.68  thf('245', plain,
% 0.47/0.68      (((((sk_F) != (sk_F))
% 0.47/0.68         | (v1_xboole_0 @ sk_D)
% 0.47/0.68         | (v1_xboole_0 @ sk_C)
% 0.47/0.68         | (v1_xboole_0 @ sk_B)
% 0.47/0.68         | (v1_xboole_0 @ sk_A)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68                = (sk_F))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['243', '244'])).
% 0.47/0.68  thf('246', plain,
% 0.47/0.68      ((((v1_xboole_0 @ sk_A)
% 0.47/0.68         | (v1_xboole_0 @ sk_B)
% 0.47/0.68         | (v1_xboole_0 @ sk_C)
% 0.47/0.68         | (v1_xboole_0 @ sk_D)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68                = (sk_F))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['245'])).
% 0.47/0.68  thf('247', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('248', plain,
% 0.47/0.68      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68                = (sk_F))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['246', '247'])).
% 0.47/0.68  thf('249', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('250', plain,
% 0.47/0.68      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68                = (sk_F))))),
% 0.47/0.68      inference('clc', [status(thm)], ['248', '249'])).
% 0.47/0.68  thf('251', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('252', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_B))
% 0.47/0.68         <= (~
% 0.47/0.68             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68                = (sk_F))))),
% 0.47/0.68      inference('clc', [status(thm)], ['250', '251'])).
% 0.47/0.68  thf('253', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('254', plain,
% 0.47/0.68      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68          = (sk_F)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['252', '253'])).
% 0.47/0.68  thf('255', plain,
% 0.47/0.68      (~
% 0.47/0.68       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68          = (sk_E))) | 
% 0.47/0.68       ~
% 0.47/0.68       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.47/0.68          = (sk_F))) | 
% 0.47/0.68       ~
% 0.47/0.68       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.47/0.68          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.47/0.68             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.47/0.68      inference('split', [status(esa)], ['200'])).
% 0.47/0.68  thf('256', plain,
% 0.47/0.68      (~
% 0.47/0.68       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68          = (sk_E)))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['215', '254', '255'])).
% 0.47/0.68  thf('257', plain,
% 0.47/0.68      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.47/0.68         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.47/0.68         != (sk_E))),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['201', '256'])).
% 0.47/0.68  thf('258', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['199', '257'])).
% 0.47/0.68  thf('259', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_D)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['15', '258'])).
% 0.47/0.68  thf('260', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_A)
% 0.47/0.68        | (v1_xboole_0 @ sk_B)
% 0.47/0.68        | (v1_xboole_0 @ sk_C)
% 0.47/0.68        | (v1_xboole_0 @ sk_D))),
% 0.47/0.68      inference('simplify', [status(thm)], ['259'])).
% 0.47/0.68  thf('261', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('262', plain,
% 0.47/0.68      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['260', '261'])).
% 0.47/0.68  thf('263', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('264', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.47/0.68      inference('clc', [status(thm)], ['262', '263'])).
% 0.47/0.68  thf('265', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('266', plain, ((v1_xboole_0 @ sk_B)),
% 0.47/0.68      inference('clc', [status(thm)], ['264', '265'])).
% 0.47/0.68  thf('267', plain, ($false), inference('demod', [status(thm)], ['0', '266'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
