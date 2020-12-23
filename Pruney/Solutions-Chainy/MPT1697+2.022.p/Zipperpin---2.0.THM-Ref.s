%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ALnRyFxG9O

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:56 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  371 (29529 expanded)
%              Number of leaves         :   44 (8494 expanded)
%              Depth                    :   63
%              Number of atoms          : 5838 (1291982 expanded)
%              Number of equality atoms :  283 (43099 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('72',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('77',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('78',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
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

thf('80',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['84','85'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('87',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('93',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('94',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['88','91','94'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k7_relat_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['89','90'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_D )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k7_relat_1 @ sk_F @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','99'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_F ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('103',plain,(
    ! [X14: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('104',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['89','90'])).

thf('105',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','70','71','76','106','107','108','109','110'])).

thf('112',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('117',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['113'])).

thf('118',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('120',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('124',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('125',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','105'])).

thf('126',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('128',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( sk_B @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k7_relat_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) @ X13 )
        = ( k7_relat_1 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X14: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf('137',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('138',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('151',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('154',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['148','151','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['149','150'])).

thf('157',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['138','155','156'])).

thf('158',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['148','151','154'])).

thf('160',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k7_relat_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['149','150'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( ( k7_relat_1 @ sk_E @ X0 )
          = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('166',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['164','168'])).

thf('170',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['126','169'])).

thf('171',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf('173',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('174',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('175',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('176',plain,(
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

thf('177',plain,(
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
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
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
    inference('sup-',[status(thm)],['175','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('187',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('189',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','105'])).

thf('190',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['178','179','180','181','182','183','184','185','186','187','188','189','190','191','192','193'])).

thf('195',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
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
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['174','195'])).

thf('197',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['173','197'])).

thf('199',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['172','199'])).

thf('201',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['148','151','154'])).

thf('202',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['149','150'])).

thf('203',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('206',plain,
    ( ( ( sk_F != sk_F )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('217',plain,
    ( ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('219',plain,
    ( ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('221',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('222',plain,
    ( ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('224',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('225',plain,
    ( ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('227',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('228',plain,
    ( ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('230',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('231',plain,
    ( ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
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
    inference(simplify,[status(thm)],['176'])).

thf('233',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ sk_D )
        = sk_F )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ( ( k2_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) )
       != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('239',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('240',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('241',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_D )
      = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('243',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('246',plain,
    ( ! [X0: $i] :
        ( ( ( k2_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_E @ X0 )
          = ( k7_relat_1 @ sk_E @ X0 ) )
        | ~ ( v1_funct_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('249',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( ( k7_relat_1 @ sk_E @ X0 )
          = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['167'])).

thf('251',plain,
    ( ! [X0: $i] :
        ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ! [X0: $i] :
        ( ( k2_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_E @ X0 )
        = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['246','251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('255',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_D )
      = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('257',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','105'])).

thf('258',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('259',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('260',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('264',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ sk_D )
        = sk_F )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['233','234','235','236','237','238','241','253','254','255','256','257','258','261','262','265'])).

thf('267',plain,
    ( ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ sk_D )
        = sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('269',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('270',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('271',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(demod,[status(thm)],['268','269','270'])).

thf('272',plain,
    ( ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['267','271'])).

thf('273',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['225','272'])).

thf('274',plain,
    ( ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F ) )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['273'])).

thf('275',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['219','274'])).

thf('276',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['278','279'])).

thf('281',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('282',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['280','283'])).

thf('285',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['113'])).

thf('288',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['171','286','287'])).

thf('289',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['114','288'])).

thf('290',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['112','289'])).

thf('291',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','290'])).

thf('292',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','292'])).

thf('294',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf('296',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['293'])).

thf('297',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['148','151','154'])).

thf('299',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['149','150'])).

thf('300',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['297','298','299'])).

thf('301',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['294','309'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('312',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['307','308'])).

thf('313',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['167'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_E @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['311','312','313'])).

thf('315',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['310','314'])).

thf('316',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['318','319'])).

thf('321',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['307','308'])).

thf('323',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['321','322'])).

thf('324',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['320','323'])).

thf('325',plain,(
    $false ),
    inference(demod,[status(thm)],['0','324'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ALnRyFxG9O
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:26:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 1.91/2.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.91/2.13  % Solved by: fo/fo7.sh
% 1.91/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.13  % done 1374 iterations in 1.689s
% 1.91/2.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.91/2.13  % SZS output start Refutation
% 1.91/2.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.91/2.13  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.91/2.13  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.91/2.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.91/2.13  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.91/2.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.91/2.13  thf(sk_F_type, type, sk_F: $i).
% 1.91/2.13  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 1.91/2.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.91/2.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.91/2.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.91/2.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.91/2.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.91/2.13  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 1.91/2.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.91/2.13  thf(sk_D_type, type, sk_D: $i).
% 1.91/2.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.91/2.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.91/2.13  thf(sk_E_type, type, sk_E: $i).
% 1.91/2.13  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.91/2.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.91/2.13  thf(sk_C_type, type, sk_C: $i).
% 1.91/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.91/2.13  thf(sk_B_type, type, sk_B: $i > $i).
% 1.91/2.13  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.91/2.13  thf(t6_tmap_1, conjecture,
% 1.91/2.13    (![A:$i]:
% 1.91/2.13     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.91/2.13       ( ![B:$i]:
% 1.91/2.13         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.91/2.13           ( ![C:$i]:
% 1.91/2.13             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.91/2.13                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.91/2.13               ( ![D:$i]:
% 1.91/2.13                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.91/2.13                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.91/2.13                   ( ( r1_subset_1 @ C @ D ) =>
% 1.91/2.13                     ( ![E:$i]:
% 1.91/2.13                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.91/2.13                           ( m1_subset_1 @
% 1.91/2.13                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.91/2.13                         ( ![F:$i]:
% 1.91/2.13                           ( ( ( v1_funct_1 @ F ) & 
% 1.91/2.13                               ( v1_funct_2 @ F @ D @ B ) & 
% 1.91/2.13                               ( m1_subset_1 @
% 1.91/2.13                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.91/2.13                             ( ( ( k2_partfun1 @
% 1.91/2.13                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.91/2.13                                 ( k2_partfun1 @
% 1.91/2.13                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.91/2.13                               ( ( k2_partfun1 @
% 1.91/2.13                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.91/2.13                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.91/2.13                                 ( E ) ) & 
% 1.91/2.13                               ( ( k2_partfun1 @
% 1.91/2.13                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.91/2.13                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.91/2.13                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.13    (~( ![A:$i]:
% 1.91/2.13        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.91/2.13          ( ![B:$i]:
% 1.91/2.13            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.91/2.13              ( ![C:$i]:
% 1.91/2.13                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.91/2.13                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.91/2.13                  ( ![D:$i]:
% 1.91/2.13                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.91/2.13                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.91/2.13                      ( ( r1_subset_1 @ C @ D ) =>
% 1.91/2.13                        ( ![E:$i]:
% 1.91/2.13                          ( ( ( v1_funct_1 @ E ) & 
% 1.91/2.13                              ( v1_funct_2 @ E @ C @ B ) & 
% 1.91/2.13                              ( m1_subset_1 @
% 1.91/2.13                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.91/2.13                            ( ![F:$i]:
% 1.91/2.13                              ( ( ( v1_funct_1 @ F ) & 
% 1.91/2.13                                  ( v1_funct_2 @ F @ D @ B ) & 
% 1.91/2.13                                  ( m1_subset_1 @
% 1.91/2.13                                    F @ 
% 1.91/2.13                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.91/2.13                                ( ( ( k2_partfun1 @
% 1.91/2.13                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.91/2.13                                    ( k2_partfun1 @
% 1.91/2.13                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.91/2.13                                  ( ( k2_partfun1 @
% 1.91/2.13                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.91/2.13                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.91/2.13                                    ( E ) ) & 
% 1.91/2.13                                  ( ( k2_partfun1 @
% 1.91/2.13                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.91/2.13                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.91/2.13                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.91/2.13    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 1.91/2.13  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('2', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('3', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(dt_k1_tmap_1, axiom,
% 1.91/2.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.91/2.13     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.91/2.13         ( ~( v1_xboole_0 @ C ) ) & 
% 1.91/2.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 1.91/2.13         ( ~( v1_xboole_0 @ D ) ) & 
% 1.91/2.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 1.91/2.13         ( v1_funct_2 @ E @ C @ B ) & 
% 1.91/2.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.91/2.13         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.91/2.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.91/2.13       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.91/2.13         ( v1_funct_2 @
% 1.91/2.13           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.91/2.13           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.91/2.13         ( m1_subset_1 @
% 1.91/2.13           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.91/2.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 1.91/2.13  thf('4', plain,
% 1.91/2.13      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.91/2.13          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 1.91/2.13          | ~ (v1_funct_1 @ X42)
% 1.91/2.13          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 1.91/2.13          | (v1_xboole_0 @ X45)
% 1.91/2.13          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 1.91/2.13          | (v1_xboole_0 @ X43)
% 1.91/2.13          | (v1_xboole_0 @ X44)
% 1.91/2.13          | (v1_xboole_0 @ X46)
% 1.91/2.13          | ~ (v1_funct_1 @ X47)
% 1.91/2.13          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 1.91/2.13          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.91/2.13          | (v1_funct_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47)))),
% 1.91/2.13      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.91/2.13  thf('5', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.13         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 1.91/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.91/2.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.91/2.13          | ~ (v1_funct_1 @ X0)
% 1.91/2.13          | (v1_xboole_0 @ X2)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 1.91/2.13          | (v1_xboole_0 @ X1)
% 1.91/2.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.91/2.13          | ~ (v1_funct_1 @ sk_E)
% 1.91/2.13          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 1.91/2.13      inference('sup-', [status(thm)], ['3', '4'])).
% 1.91/2.13  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('8', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.13         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 1.91/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 1.91/2.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 1.91/2.13          | ~ (v1_funct_1 @ X0)
% 1.91/2.13          | (v1_xboole_0 @ X2)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 1.91/2.13          | (v1_xboole_0 @ X1)
% 1.91/2.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.91/2.13      inference('demod', [status(thm)], ['5', '6', '7'])).
% 1.91/2.13  thf('9', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_D)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (v1_funct_1 @ sk_F)
% 1.91/2.13          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.13          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.91/2.13      inference('sup-', [status(thm)], ['2', '8'])).
% 1.91/2.13  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('12', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_D)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 1.91/2.13      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.91/2.13  thf('13', plain,
% 1.91/2.13      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.13        | (v1_xboole_0 @ sk_D))),
% 1.91/2.13      inference('sup-', [status(thm)], ['1', '12'])).
% 1.91/2.13  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('15', plain,
% 1.91/2.13      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | (v1_xboole_0 @ sk_D))),
% 1.91/2.13      inference('demod', [status(thm)], ['13', '14'])).
% 1.91/2.13  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('17', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('18', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('19', plain,
% 1.91/2.13      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.91/2.13          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 1.91/2.13          | ~ (v1_funct_1 @ X42)
% 1.91/2.13          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 1.91/2.13          | (v1_xboole_0 @ X45)
% 1.91/2.13          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 1.91/2.13          | (v1_xboole_0 @ X43)
% 1.91/2.13          | (v1_xboole_0 @ X44)
% 1.91/2.13          | (v1_xboole_0 @ X46)
% 1.91/2.13          | ~ (v1_funct_1 @ X47)
% 1.91/2.13          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 1.91/2.13          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.91/2.13          | (v1_funct_2 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 1.91/2.13             (k4_subset_1 @ X46 @ X43 @ X45) @ X44))),
% 1.91/2.13      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.91/2.13  thf('20', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.13         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.91/2.13           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 1.91/2.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.91/2.13          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.91/2.13          | ~ (v1_funct_1 @ X2)
% 1.91/2.13          | (v1_xboole_0 @ X1)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.91/2.13          | ~ (v1_funct_1 @ sk_E)
% 1.91/2.13          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 1.91/2.13      inference('sup-', [status(thm)], ['18', '19'])).
% 1.91/2.13  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('23', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.13         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.91/2.13           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 1.91/2.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.91/2.13          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.91/2.13          | ~ (v1_funct_1 @ X2)
% 1.91/2.13          | (v1_xboole_0 @ X1)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.91/2.13      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.91/2.13  thf('24', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_D)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (v1_funct_1 @ sk_F)
% 1.91/2.13          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.13          | (v1_funct_2 @ 
% 1.91/2.13             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 1.91/2.13      inference('sup-', [status(thm)], ['17', '23'])).
% 1.91/2.13  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('27', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_D)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | (v1_funct_2 @ 
% 1.91/2.13             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 1.91/2.13      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.91/2.13  thf('28', plain,
% 1.91/2.13      (((v1_funct_2 @ 
% 1.91/2.13         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.13        | (v1_xboole_0 @ sk_D))),
% 1.91/2.13      inference('sup-', [status(thm)], ['16', '27'])).
% 1.91/2.13  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('30', plain,
% 1.91/2.13      (((v1_funct_2 @ 
% 1.91/2.13         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | (v1_xboole_0 @ sk_D))),
% 1.91/2.13      inference('demod', [status(thm)], ['28', '29'])).
% 1.91/2.13  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('32', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('33', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('34', plain,
% 1.91/2.13      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.91/2.13          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 1.91/2.13          | ~ (v1_funct_1 @ X42)
% 1.91/2.13          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 1.91/2.13          | (v1_xboole_0 @ X45)
% 1.91/2.13          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 1.91/2.13          | (v1_xboole_0 @ X43)
% 1.91/2.13          | (v1_xboole_0 @ X44)
% 1.91/2.13          | (v1_xboole_0 @ X46)
% 1.91/2.13          | ~ (v1_funct_1 @ X47)
% 1.91/2.13          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 1.91/2.13          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.91/2.13          | (m1_subset_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 1.91/2.13             (k1_zfmisc_1 @ 
% 1.91/2.13              (k2_zfmisc_1 @ (k4_subset_1 @ X46 @ X43 @ X45) @ X44))))),
% 1.91/2.13      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.91/2.13  thf('35', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.13         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.91/2.13           (k1_zfmisc_1 @ 
% 1.91/2.13            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 1.91/2.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.91/2.13          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.91/2.13          | ~ (v1_funct_1 @ X2)
% 1.91/2.13          | (v1_xboole_0 @ X1)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.91/2.13          | ~ (v1_funct_1 @ sk_E)
% 1.91/2.13          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 1.91/2.13      inference('sup-', [status(thm)], ['33', '34'])).
% 1.91/2.13  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('38', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.13         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 1.91/2.13           (k1_zfmisc_1 @ 
% 1.91/2.13            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 1.91/2.13          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 1.91/2.13          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 1.91/2.13          | ~ (v1_funct_1 @ X2)
% 1.91/2.13          | (v1_xboole_0 @ X1)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.91/2.13      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.91/2.13  thf('39', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_D)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | ~ (v1_funct_1 @ sk_F)
% 1.91/2.13          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.13          | (m1_subset_1 @ 
% 1.91/2.13             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13             (k1_zfmisc_1 @ 
% 1.91/2.13              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 1.91/2.13      inference('sup-', [status(thm)], ['32', '38'])).
% 1.91/2.13  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('42', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_D)
% 1.91/2.13          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 1.91/2.13          | (v1_xboole_0 @ sk_C)
% 1.91/2.13          | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13          | (v1_xboole_0 @ X0)
% 1.91/2.13          | (m1_subset_1 @ 
% 1.91/2.13             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13             (k1_zfmisc_1 @ 
% 1.91/2.13              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 1.91/2.13      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.91/2.13  thf('43', plain,
% 1.91/2.13      (((m1_subset_1 @ 
% 1.91/2.13         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13         (k1_zfmisc_1 @ 
% 1.91/2.13          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.13        | (v1_xboole_0 @ sk_D))),
% 1.91/2.13      inference('sup-', [status(thm)], ['31', '42'])).
% 1.91/2.13  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('45', plain,
% 1.91/2.13      (((m1_subset_1 @ 
% 1.91/2.13         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13         (k1_zfmisc_1 @ 
% 1.91/2.13          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | (v1_xboole_0 @ sk_D))),
% 1.91/2.13      inference('demod', [status(thm)], ['43', '44'])).
% 1.91/2.13  thf(d1_tmap_1, axiom,
% 1.91/2.13    (![A:$i]:
% 1.91/2.13     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.91/2.13       ( ![B:$i]:
% 1.91/2.13         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.91/2.13           ( ![C:$i]:
% 1.91/2.13             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.91/2.13                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.91/2.13               ( ![D:$i]:
% 1.91/2.13                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.91/2.13                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.91/2.13                   ( ![E:$i]:
% 1.91/2.13                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.91/2.13                         ( m1_subset_1 @
% 1.91/2.13                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.91/2.13                       ( ![F:$i]:
% 1.91/2.13                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.91/2.13                             ( m1_subset_1 @
% 1.91/2.13                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.91/2.13                           ( ( ( k2_partfun1 @
% 1.91/2.13                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.91/2.13                               ( k2_partfun1 @
% 1.91/2.13                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 1.91/2.13                             ( ![G:$i]:
% 1.91/2.13                               ( ( ( v1_funct_1 @ G ) & 
% 1.91/2.13                                   ( v1_funct_2 @
% 1.91/2.13                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.91/2.13                                   ( m1_subset_1 @
% 1.91/2.13                                     G @ 
% 1.91/2.13                                     ( k1_zfmisc_1 @
% 1.91/2.13                                       ( k2_zfmisc_1 @
% 1.91/2.13                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 1.91/2.13                                 ( ( ( G ) =
% 1.91/2.13                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.91/2.13                                   ( ( ( k2_partfun1 @
% 1.91/2.13                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.91/2.13                                         C ) =
% 1.91/2.13                                       ( E ) ) & 
% 1.91/2.13                                     ( ( k2_partfun1 @
% 1.91/2.13                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.91/2.13                                         D ) =
% 1.91/2.13                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.13  thf('46', plain,
% 1.91/2.13      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.91/2.13         ((v1_xboole_0 @ X35)
% 1.91/2.13          | (v1_xboole_0 @ X36)
% 1.91/2.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.91/2.13          | ~ (v1_funct_1 @ X38)
% 1.91/2.13          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 1.91/2.13          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.91/2.13          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 1.91/2.13          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X40)
% 1.91/2.13              = (X39))
% 1.91/2.13          | ~ (m1_subset_1 @ X41 @ 
% 1.91/2.13               (k1_zfmisc_1 @ 
% 1.91/2.13                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 1.91/2.13          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 1.91/2.13          | ~ (v1_funct_1 @ X41)
% 1.91/2.13          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 1.91/2.13              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 1.91/2.13                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 1.91/2.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 1.91/2.13          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 1.91/2.13          | ~ (v1_funct_1 @ X39)
% 1.91/2.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 1.91/2.13          | (v1_xboole_0 @ X40)
% 1.91/2.13          | (v1_xboole_0 @ X37))),
% 1.91/2.13      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.91/2.13  thf('47', plain,
% 1.91/2.13      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.91/2.13         ((v1_xboole_0 @ X37)
% 1.91/2.13          | (v1_xboole_0 @ X40)
% 1.91/2.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 1.91/2.13          | ~ (v1_funct_1 @ X39)
% 1.91/2.13          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 1.91/2.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 1.91/2.13          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 1.91/2.13              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 1.91/2.13                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 1.91/2.13          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 1.91/2.13          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 1.91/2.13               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 1.91/2.13          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 1.91/2.13               (k1_zfmisc_1 @ 
% 1.91/2.13                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 1.91/2.13          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 1.91/2.13              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X40) = (
% 1.91/2.13              X39))
% 1.91/2.13          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.91/2.13          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 1.91/2.13          | ~ (v1_funct_1 @ X38)
% 1.91/2.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.91/2.13          | (v1_xboole_0 @ X36)
% 1.91/2.13          | (v1_xboole_0 @ X35))),
% 1.91/2.13      inference('simplify', [status(thm)], ['46'])).
% 1.91/2.13  thf('48', plain,
% 1.91/2.13      (((v1_xboole_0 @ sk_D)
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_A)
% 1.91/2.13        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | (v1_xboole_0 @ sk_D)
% 1.91/2.13        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.13        | ~ (v1_funct_1 @ sk_F)
% 1.91/2.13        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.13        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 1.91/2.13        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.13            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.13            = (sk_E))
% 1.91/2.13        | ~ (v1_funct_2 @ 
% 1.91/2.13             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.13             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.13        | ~ (v1_funct_1 @ 
% 1.91/2.13             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.13        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.13            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.13            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.13                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.91/2.13        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 1.91/2.13        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 1.91/2.13        | ~ (v1_funct_1 @ sk_E)
% 1.91/2.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.13        | (v1_xboole_0 @ sk_C)
% 1.91/2.13        | (v1_xboole_0 @ sk_A))),
% 1.91/2.13      inference('sup-', [status(thm)], ['45', '47'])).
% 1.91/2.13  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('52', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(redefinition_k9_subset_1, axiom,
% 1.91/2.13    (![A:$i,B:$i,C:$i]:
% 1.91/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.91/2.13       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.91/2.13  thf('54', plain,
% 1.91/2.13      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.91/2.13         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 1.91/2.13          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.91/2.13      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.91/2.13  thf('55', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.13      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.13  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(redefinition_r1_subset_1, axiom,
% 1.91/2.13    (![A:$i,B:$i]:
% 1.91/2.13     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.91/2.13       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 1.91/2.13  thf('57', plain,
% 1.91/2.13      (![X17 : $i, X18 : $i]:
% 1.91/2.13         ((v1_xboole_0 @ X17)
% 1.91/2.13          | (v1_xboole_0 @ X18)
% 1.91/2.13          | (r1_xboole_0 @ X17 @ X18)
% 1.91/2.13          | ~ (r1_subset_1 @ X17 @ X18))),
% 1.91/2.13      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 1.91/2.13  thf('58', plain,
% 1.91/2.13      (((r1_xboole_0 @ sk_C @ sk_D)
% 1.91/2.13        | (v1_xboole_0 @ sk_D)
% 1.91/2.13        | (v1_xboole_0 @ sk_C))),
% 1.91/2.13      inference('sup-', [status(thm)], ['56', '57'])).
% 1.91/2.13  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 1.91/2.13      inference('clc', [status(thm)], ['58', '59'])).
% 1.91/2.13  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.91/2.13      inference('clc', [status(thm)], ['60', '61'])).
% 1.91/2.13  thf(d7_xboole_0, axiom,
% 1.91/2.13    (![A:$i,B:$i]:
% 1.91/2.13     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.91/2.13       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.91/2.13  thf('63', plain,
% 1.91/2.13      (![X0 : $i, X1 : $i]:
% 1.91/2.13         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.91/2.13      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.91/2.13  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.13      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.13  thf('65', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(redefinition_k2_partfun1, axiom,
% 1.91/2.13    (![A:$i,B:$i,C:$i,D:$i]:
% 1.91/2.13     ( ( ( v1_funct_1 @ C ) & 
% 1.91/2.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.91/2.13       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.91/2.13  thf('66', plain,
% 1.91/2.13      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.91/2.13          | ~ (v1_funct_1 @ X31)
% 1.91/2.13          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 1.91/2.13      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.91/2.13  thf('67', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 1.91/2.13          | ~ (v1_funct_1 @ sk_E))),
% 1.91/2.13      inference('sup-', [status(thm)], ['65', '66'])).
% 1.91/2.13  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('69', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.91/2.13      inference('demod', [status(thm)], ['67', '68'])).
% 1.91/2.13  thf('70', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.13      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.13  thf('71', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.13      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.13  thf('72', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('73', plain,
% 1.91/2.13      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.91/2.13          | ~ (v1_funct_1 @ X31)
% 1.91/2.13          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 1.91/2.13      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.91/2.13  thf('74', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 1.91/2.13          | ~ (v1_funct_1 @ sk_F))),
% 1.91/2.13      inference('sup-', [status(thm)], ['72', '73'])).
% 1.91/2.13  thf('75', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('76', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.91/2.13      inference('demod', [status(thm)], ['74', '75'])).
% 1.91/2.13  thf(t2_boole, axiom,
% 1.91/2.13    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.91/2.13  thf('77', plain,
% 1.91/2.13      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.91/2.13      inference('cnf', [status(esa)], [t2_boole])).
% 1.91/2.13  thf('78', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 1.91/2.13      inference('clc', [status(thm)], ['60', '61'])).
% 1.91/2.13  thf('79', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(cc5_funct_2, axiom,
% 1.91/2.13    (![A:$i,B:$i]:
% 1.91/2.13     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.91/2.13       ( ![C:$i]:
% 1.91/2.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.13           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.91/2.13             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.91/2.13  thf('80', plain,
% 1.91/2.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.91/2.13         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.91/2.13          | (v1_partfun1 @ X26 @ X27)
% 1.91/2.13          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 1.91/2.13          | ~ (v1_funct_1 @ X26)
% 1.91/2.13          | (v1_xboole_0 @ X28))),
% 1.91/2.13      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.91/2.13  thf('81', plain,
% 1.91/2.13      (((v1_xboole_0 @ sk_B_1)
% 1.91/2.13        | ~ (v1_funct_1 @ sk_F)
% 1.91/2.13        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.13        | (v1_partfun1 @ sk_F @ sk_D))),
% 1.91/2.13      inference('sup-', [status(thm)], ['79', '80'])).
% 1.91/2.13  thf('82', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('83', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('84', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_F @ sk_D))),
% 1.91/2.13      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.91/2.13  thf('85', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf('86', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 1.91/2.13      inference('clc', [status(thm)], ['84', '85'])).
% 1.91/2.13  thf(d4_partfun1, axiom,
% 1.91/2.13    (![A:$i,B:$i]:
% 1.91/2.13     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.91/2.13       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.91/2.13  thf('87', plain,
% 1.91/2.13      (![X29 : $i, X30 : $i]:
% 1.91/2.13         (~ (v1_partfun1 @ X30 @ X29)
% 1.91/2.13          | ((k1_relat_1 @ X30) = (X29))
% 1.91/2.13          | ~ (v4_relat_1 @ X30 @ X29)
% 1.91/2.13          | ~ (v1_relat_1 @ X30))),
% 1.91/2.13      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.91/2.13  thf('88', plain,
% 1.91/2.13      ((~ (v1_relat_1 @ sk_F)
% 1.91/2.13        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 1.91/2.13        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 1.91/2.13      inference('sup-', [status(thm)], ['86', '87'])).
% 1.91/2.13  thf('89', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(cc1_relset_1, axiom,
% 1.91/2.13    (![A:$i,B:$i,C:$i]:
% 1.91/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.13       ( v1_relat_1 @ C ) ))).
% 1.91/2.13  thf('90', plain,
% 1.91/2.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.91/2.13         ((v1_relat_1 @ X19)
% 1.91/2.13          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.91/2.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.91/2.13  thf('91', plain, ((v1_relat_1 @ sk_F)),
% 1.91/2.13      inference('sup-', [status(thm)], ['89', '90'])).
% 1.91/2.13  thf('92', plain,
% 1.91/2.13      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.13  thf(cc2_relset_1, axiom,
% 1.91/2.13    (![A:$i,B:$i,C:$i]:
% 1.91/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.91/2.13  thf('93', plain,
% 1.91/2.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.91/2.13         ((v4_relat_1 @ X22 @ X23)
% 1.91/2.13          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.91/2.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.91/2.13  thf('94', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 1.91/2.13      inference('sup-', [status(thm)], ['92', '93'])).
% 1.91/2.13  thf('95', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 1.91/2.13      inference('demod', [status(thm)], ['88', '91', '94'])).
% 1.91/2.13  thf(t187_relat_1, axiom,
% 1.91/2.13    (![A:$i]:
% 1.91/2.13     ( ( v1_relat_1 @ A ) =>
% 1.91/2.13       ( ![B:$i]:
% 1.91/2.13         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 1.91/2.13           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.91/2.13  thf('96', plain,
% 1.91/2.13      (![X15 : $i, X16 : $i]:
% 1.91/2.13         (~ (r1_xboole_0 @ X15 @ (k1_relat_1 @ X16))
% 1.91/2.13          | ((k7_relat_1 @ X16 @ X15) = (k1_xboole_0))
% 1.91/2.13          | ~ (v1_relat_1 @ X16))),
% 1.91/2.13      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.91/2.13  thf('97', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (r1_xboole_0 @ X0 @ sk_D)
% 1.91/2.13          | ~ (v1_relat_1 @ sk_F)
% 1.91/2.13          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 1.91/2.13      inference('sup-', [status(thm)], ['95', '96'])).
% 1.91/2.13  thf('98', plain, ((v1_relat_1 @ sk_F)),
% 1.91/2.13      inference('sup-', [status(thm)], ['89', '90'])).
% 1.91/2.13  thf('99', plain,
% 1.91/2.13      (![X0 : $i]:
% 1.91/2.13         (~ (r1_xboole_0 @ X0 @ sk_D)
% 1.91/2.13          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 1.91/2.13      inference('demod', [status(thm)], ['97', '98'])).
% 1.91/2.13  thf('100', plain, (((k7_relat_1 @ sk_F @ sk_C) = (k1_xboole_0))),
% 1.91/2.13      inference('sup-', [status(thm)], ['78', '99'])).
% 1.91/2.13  thf(t100_relat_1, axiom,
% 1.91/2.13    (![A:$i,B:$i,C:$i]:
% 1.91/2.13     ( ( v1_relat_1 @ C ) =>
% 1.91/2.13       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.91/2.13         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.91/2.13  thf('101', plain,
% 1.91/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.91/2.13         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 1.91/2.13            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 1.91/2.13          | ~ (v1_relat_1 @ X11))),
% 1.91/2.13      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.91/2.14  thf('102', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 1.91/2.14            = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ X0)))
% 1.91/2.14          | ~ (v1_relat_1 @ sk_F))),
% 1.91/2.14      inference('sup+', [status(thm)], ['100', '101'])).
% 1.91/2.14  thf(t111_relat_1, axiom,
% 1.91/2.14    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.91/2.14  thf('103', plain,
% 1.91/2.14      (![X14 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 1.91/2.14      inference('cnf', [status(esa)], [t111_relat_1])).
% 1.91/2.14  thf('104', plain, ((v1_relat_1 @ sk_F)),
% 1.91/2.14      inference('sup-', [status(thm)], ['89', '90'])).
% 1.91/2.14  thf('105', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k1_xboole_0) = (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ X0)))),
% 1.91/2.14      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.91/2.14  thf('106', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 1.91/2.14      inference('sup+', [status(thm)], ['77', '105'])).
% 1.91/2.14  thf('107', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('108', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('109', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('110', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('111', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14            = (sk_E))
% 1.91/2.14        | ~ (v1_funct_2 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('demod', [status(thm)],
% 1.91/2.14                ['48', '49', '50', '51', '52', '55', '64', '69', '70', '71', 
% 1.91/2.14                 '76', '106', '107', '108', '109', '110'])).
% 1.91/2.14  thf('112', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ~ (v1_funct_2 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14            = (sk_E))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['111'])).
% 1.91/2.14  thf('113', plain,
% 1.91/2.14      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14            != (sk_E))
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            != (sk_F)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('114', plain,
% 1.91/2.14      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14          != (sk_E)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14                = (sk_E))))),
% 1.91/2.14      inference('split', [status(esa)], ['113'])).
% 1.91/2.14  thf('115', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.91/2.14      inference('demod', [status(thm)], ['74', '75'])).
% 1.91/2.14  thf('116', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.14  thf('117', plain,
% 1.91/2.14      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('split', [status(esa)], ['113'])).
% 1.91/2.14  thf('118', plain,
% 1.91/2.14      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['116', '117'])).
% 1.91/2.14  thf('119', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.14  thf('120', plain,
% 1.91/2.14      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 1.91/2.14          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('demod', [status(thm)], ['118', '119'])).
% 1.91/2.14  thf('121', plain,
% 1.91/2.14      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 1.91/2.14          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['115', '120'])).
% 1.91/2.14  thf('122', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.14  thf('123', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.91/2.14      inference('demod', [status(thm)], ['67', '68'])).
% 1.91/2.14  thf('124', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.14  thf('125', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 1.91/2.14      inference('sup+', [status(thm)], ['77', '105'])).
% 1.91/2.14  thf('126', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 1.91/2.14  thf('127', plain,
% 1.91/2.14      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.91/2.14      inference('cnf', [status(esa)], [t2_boole])).
% 1.91/2.14  thf(t1_mcart_1, axiom,
% 1.91/2.14    (![A:$i]:
% 1.91/2.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.91/2.14          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 1.91/2.14  thf('128', plain,
% 1.91/2.14      (![X25 : $i]:
% 1.91/2.14         (((X25) = (k1_xboole_0)) | (r1_xboole_0 @ (sk_B @ X25) @ X25))),
% 1.91/2.14      inference('cnf', [status(esa)], [t1_mcart_1])).
% 1.91/2.14  thf('129', plain,
% 1.91/2.14      (![X15 : $i, X16 : $i]:
% 1.91/2.14         (~ (r1_xboole_0 @ X15 @ (k1_relat_1 @ X16))
% 1.91/2.14          | ((k7_relat_1 @ X16 @ X15) = (k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X16))),
% 1.91/2.14      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.91/2.14  thf('130', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X0)
% 1.91/2.14          | ((k7_relat_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) = (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['128', '129'])).
% 1.91/2.14  thf('131', plain,
% 1.91/2.14      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.91/2.14         (((k7_relat_1 @ (k7_relat_1 @ X11 @ X12) @ X13)
% 1.91/2.14            = (k7_relat_1 @ X11 @ (k3_xboole_0 @ X12 @ X13)))
% 1.91/2.14          | ~ (v1_relat_1 @ X11))),
% 1.91/2.14      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.91/2.14  thf('132', plain,
% 1.91/2.14      (![X0 : $i, X1 : $i]:
% 1.91/2.14         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 1.91/2.14            = (k7_relat_1 @ X1 @ 
% 1.91/2.14               (k3_xboole_0 @ (sk_B @ (k1_relat_1 @ X1)) @ X0)))
% 1.91/2.14          | ~ (v1_relat_1 @ X1)
% 1.91/2.14          | ((k1_relat_1 @ X1) = (k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X1))),
% 1.91/2.14      inference('sup+', [status(thm)], ['130', '131'])).
% 1.91/2.14  thf('133', plain,
% 1.91/2.14      (![X14 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 1.91/2.14      inference('cnf', [status(esa)], [t111_relat_1])).
% 1.91/2.14  thf('134', plain,
% 1.91/2.14      (![X0 : $i, X1 : $i]:
% 1.91/2.14         (((k1_xboole_0)
% 1.91/2.14            = (k7_relat_1 @ X1 @ 
% 1.91/2.14               (k3_xboole_0 @ (sk_B @ (k1_relat_1 @ X1)) @ X0)))
% 1.91/2.14          | ~ (v1_relat_1 @ X1)
% 1.91/2.14          | ((k1_relat_1 @ X1) = (k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X1))),
% 1.91/2.14      inference('demod', [status(thm)], ['132', '133'])).
% 1.91/2.14  thf('135', plain,
% 1.91/2.14      (![X0 : $i, X1 : $i]:
% 1.91/2.14         (((k1_relat_1 @ X1) = (k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X1)
% 1.91/2.14          | ((k1_xboole_0)
% 1.91/2.14              = (k7_relat_1 @ X1 @ 
% 1.91/2.14                 (k3_xboole_0 @ (sk_B @ (k1_relat_1 @ X1)) @ X0))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['134'])).
% 1.91/2.14  thf('136', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X0)
% 1.91/2.14          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('sup+', [status(thm)], ['127', '135'])).
% 1.91/2.14  thf('137', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 1.91/2.14  thf('138', plain,
% 1.91/2.14      (((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14         | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.91/2.14         | ~ (v1_relat_1 @ sk_E)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['136', '137'])).
% 1.91/2.14  thf('139', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('140', plain,
% 1.91/2.14      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.91/2.14         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.91/2.14          | (v1_partfun1 @ X26 @ X27)
% 1.91/2.14          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 1.91/2.14          | ~ (v1_funct_1 @ X26)
% 1.91/2.14          | (v1_xboole_0 @ X28))),
% 1.91/2.14      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.91/2.14  thf('141', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | ~ (v1_funct_1 @ sk_E)
% 1.91/2.14        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 1.91/2.14        | (v1_partfun1 @ sk_E @ sk_C))),
% 1.91/2.14      inference('sup-', [status(thm)], ['139', '140'])).
% 1.91/2.14  thf('142', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('143', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('144', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_E @ sk_C))),
% 1.91/2.14      inference('demod', [status(thm)], ['141', '142', '143'])).
% 1.91/2.14  thf('145', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('146', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 1.91/2.14      inference('clc', [status(thm)], ['144', '145'])).
% 1.91/2.14  thf('147', plain,
% 1.91/2.14      (![X29 : $i, X30 : $i]:
% 1.91/2.14         (~ (v1_partfun1 @ X30 @ X29)
% 1.91/2.14          | ((k1_relat_1 @ X30) = (X29))
% 1.91/2.14          | ~ (v4_relat_1 @ X30 @ X29)
% 1.91/2.14          | ~ (v1_relat_1 @ X30))),
% 1.91/2.14      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.91/2.14  thf('148', plain,
% 1.91/2.14      ((~ (v1_relat_1 @ sk_E)
% 1.91/2.14        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 1.91/2.14        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['146', '147'])).
% 1.91/2.14  thf('149', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('150', plain,
% 1.91/2.14      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.91/2.14         ((v1_relat_1 @ X19)
% 1.91/2.14          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.91/2.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.91/2.14  thf('151', plain, ((v1_relat_1 @ sk_E)),
% 1.91/2.14      inference('sup-', [status(thm)], ['149', '150'])).
% 1.91/2.14  thf('152', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('153', plain,
% 1.91/2.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.91/2.14         ((v4_relat_1 @ X22 @ X23)
% 1.91/2.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.91/2.14      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.91/2.14  thf('154', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 1.91/2.14      inference('sup-', [status(thm)], ['152', '153'])).
% 1.91/2.14  thf('155', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.91/2.14      inference('demod', [status(thm)], ['148', '151', '154'])).
% 1.91/2.14  thf('156', plain, ((v1_relat_1 @ sk_E)),
% 1.91/2.14      inference('sup-', [status(thm)], ['149', '150'])).
% 1.91/2.14  thf('157', plain,
% 1.91/2.14      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('demod', [status(thm)], ['138', '155', '156'])).
% 1.91/2.14  thf('158', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['157'])).
% 1.91/2.14  thf('159', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.91/2.14      inference('demod', [status(thm)], ['148', '151', '154'])).
% 1.91/2.14  thf('160', plain,
% 1.91/2.14      (![X15 : $i, X16 : $i]:
% 1.91/2.14         (~ (r1_xboole_0 @ X15 @ (k1_relat_1 @ X16))
% 1.91/2.14          | ((k7_relat_1 @ X16 @ X15) = (k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X16))),
% 1.91/2.14      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.91/2.14  thf('161', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.91/2.14          | ~ (v1_relat_1 @ sk_E)
% 1.91/2.14          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['159', '160'])).
% 1.91/2.14  thf('162', plain, ((v1_relat_1 @ sk_E)),
% 1.91/2.14      inference('sup-', [status(thm)], ['149', '150'])).
% 1.91/2.14  thf('163', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.91/2.14          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('demod', [status(thm)], ['161', '162'])).
% 1.91/2.14  thf('164', plain,
% 1.91/2.14      ((![X0 : $i]:
% 1.91/2.14          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.91/2.14           | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['158', '163'])).
% 1.91/2.14  thf('165', plain,
% 1.91/2.14      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.91/2.14      inference('cnf', [status(esa)], [t2_boole])).
% 1.91/2.14  thf('166', plain,
% 1.91/2.14      (![X0 : $i, X2 : $i]:
% 1.91/2.14         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.91/2.14      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.91/2.14  thf('167', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['165', '166'])).
% 1.91/2.14  thf('168', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.91/2.14      inference('simplify', [status(thm)], ['167'])).
% 1.91/2.14  thf('169', plain,
% 1.91/2.14      ((![X0 : $i]: ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('demod', [status(thm)], ['164', '168'])).
% 1.91/2.14  thf('170', plain,
% 1.91/2.14      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 1.91/2.14      inference('demod', [status(thm)], ['126', '169'])).
% 1.91/2.14  thf('171', plain,
% 1.91/2.14      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['170'])).
% 1.91/2.14  thf('172', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X0)
% 1.91/2.14          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('sup+', [status(thm)], ['127', '135'])).
% 1.91/2.14  thf('173', plain,
% 1.91/2.14      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['13', '14'])).
% 1.91/2.14  thf('174', plain,
% 1.91/2.14      (((v1_funct_2 @ 
% 1.91/2.14         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['28', '29'])).
% 1.91/2.14  thf('175', plain,
% 1.91/2.14      (((m1_subset_1 @ 
% 1.91/2.14         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14         (k1_zfmisc_1 @ 
% 1.91/2.14          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['43', '44'])).
% 1.91/2.14  thf('176', plain,
% 1.91/2.14      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.91/2.14         ((v1_xboole_0 @ X35)
% 1.91/2.14          | (v1_xboole_0 @ X36)
% 1.91/2.14          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.91/2.14          | ~ (v1_funct_1 @ X38)
% 1.91/2.14          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 1.91/2.14          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.91/2.14          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 1.91/2.14          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X36)
% 1.91/2.14              = (X38))
% 1.91/2.14          | ~ (m1_subset_1 @ X41 @ 
% 1.91/2.14               (k1_zfmisc_1 @ 
% 1.91/2.14                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 1.91/2.14          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 1.91/2.14          | ~ (v1_funct_1 @ X41)
% 1.91/2.14          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 1.91/2.14              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 1.91/2.14                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 1.91/2.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 1.91/2.14          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 1.91/2.14          | ~ (v1_funct_1 @ X39)
% 1.91/2.14          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 1.91/2.14          | (v1_xboole_0 @ X40)
% 1.91/2.14          | (v1_xboole_0 @ X37))),
% 1.91/2.14      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.91/2.14  thf('177', plain,
% 1.91/2.14      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.91/2.14         ((v1_xboole_0 @ X37)
% 1.91/2.14          | (v1_xboole_0 @ X40)
% 1.91/2.14          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 1.91/2.14          | ~ (v1_funct_1 @ X39)
% 1.91/2.14          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 1.91/2.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 1.91/2.14          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 1.91/2.14              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 1.91/2.14                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 1.91/2.14          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 1.91/2.14          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 1.91/2.14               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 1.91/2.14          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 1.91/2.14               (k1_zfmisc_1 @ 
% 1.91/2.14                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 1.91/2.14          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 1.91/2.14              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X36) = (
% 1.91/2.14              X38))
% 1.91/2.14          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.91/2.14          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 1.91/2.14          | ~ (v1_funct_1 @ X38)
% 1.91/2.14          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.91/2.14          | (v1_xboole_0 @ X36)
% 1.91/2.14          | (v1_xboole_0 @ X35))),
% 1.91/2.14      inference('simplify', [status(thm)], ['176'])).
% 1.91/2.14  thf('178', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.14        | ~ (v1_funct_1 @ sk_F)
% 1.91/2.14        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.14        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | ~ (v1_funct_2 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 1.91/2.14        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 1.91/2.14        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 1.91/2.14        | ~ (v1_funct_1 @ sk_E)
% 1.91/2.14        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('sup-', [status(thm)], ['175', '177'])).
% 1.91/2.14  thf('179', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('180', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('181', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('182', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('183', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.14  thf('184', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.14  thf('185', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.91/2.14      inference('demod', [status(thm)], ['67', '68'])).
% 1.91/2.14  thf('186', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.14  thf('187', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.14  thf('188', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.91/2.14      inference('demod', [status(thm)], ['74', '75'])).
% 1.91/2.14  thf('189', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 1.91/2.14      inference('sup+', [status(thm)], ['77', '105'])).
% 1.91/2.14  thf('190', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('191', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('192', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('193', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('194', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | ~ (v1_funct_2 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('demod', [status(thm)],
% 1.91/2.14                ['178', '179', '180', '181', '182', '183', '184', '185', 
% 1.91/2.14                 '186', '187', '188', '189', '190', '191', '192', '193'])).
% 1.91/2.14  thf('195', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ~ (v1_funct_2 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['194'])).
% 1.91/2.14  thf('196', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['174', '195'])).
% 1.91/2.14  thf('197', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['196'])).
% 1.91/2.14  thf('198', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | ((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['173', '197'])).
% 1.91/2.14  thf('199', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['198'])).
% 1.91/2.14  thf('200', plain,
% 1.91/2.14      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.91/2.14        | ~ (v1_relat_1 @ sk_E)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['172', '199'])).
% 1.91/2.14  thf('201', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.91/2.14      inference('demod', [status(thm)], ['148', '151', '154'])).
% 1.91/2.14  thf('202', plain, ((v1_relat_1 @ sk_E)),
% 1.91/2.14      inference('sup-', [status(thm)], ['149', '150'])).
% 1.91/2.14  thf('203', plain,
% 1.91/2.14      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ((sk_C) = (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14            = (sk_F)))),
% 1.91/2.14      inference('demod', [status(thm)], ['200', '201', '202'])).
% 1.91/2.14  thf('204', plain,
% 1.91/2.14      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14          = (sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | ((sk_C) = (k1_xboole_0)))),
% 1.91/2.14      inference('simplify', [status(thm)], ['203'])).
% 1.91/2.14  thf('205', plain,
% 1.91/2.14      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14          != (sk_F)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('split', [status(esa)], ['113'])).
% 1.91/2.14  thf('206', plain,
% 1.91/2.14      (((((sk_F) != (sk_F))
% 1.91/2.14         | ((sk_C) = (k1_xboole_0))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_C)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['204', '205'])).
% 1.91/2.14  thf('207', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_C)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | ((sk_C) = (k1_xboole_0))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['206'])).
% 1.91/2.14  thf('208', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('209', plain,
% 1.91/2.14      (((((sk_C) = (k1_xboole_0))
% 1.91/2.14         | (v1_xboole_0 @ sk_C)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['207', '208'])).
% 1.91/2.14  thf('210', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('211', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | ((sk_C) = (k1_xboole_0))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['209', '210'])).
% 1.91/2.14  thf('212', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('213', plain,
% 1.91/2.14      (((((sk_C) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['211', '212'])).
% 1.91/2.14  thf('214', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('215', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('216', plain,
% 1.91/2.14      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['13', '14'])).
% 1.91/2.14  thf('217', plain,
% 1.91/2.14      ((((v1_funct_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_C)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['215', '216'])).
% 1.91/2.14  thf('218', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('219', plain,
% 1.91/2.14      ((((v1_funct_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)], ['217', '218'])).
% 1.91/2.14  thf('220', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('221', plain,
% 1.91/2.14      (((v1_funct_2 @ 
% 1.91/2.14         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['28', '29'])).
% 1.91/2.14  thf('222', plain,
% 1.91/2.14      ((((v1_funct_2 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14          (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_C)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['220', '221'])).
% 1.91/2.14  thf('223', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('224', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('225', plain,
% 1.91/2.14      ((((v1_funct_2 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14          (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)], ['222', '223', '224'])).
% 1.91/2.14  thf('226', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('227', plain,
% 1.91/2.14      (((m1_subset_1 @ 
% 1.91/2.14         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14         (k1_zfmisc_1 @ 
% 1.91/2.14          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['43', '44'])).
% 1.91/2.14  thf('228', plain,
% 1.91/2.14      ((((m1_subset_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14          (k1_zfmisc_1 @ 
% 1.91/2.14           (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_C)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['226', '227'])).
% 1.91/2.14  thf('229', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('230', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('231', plain,
% 1.91/2.14      ((((m1_subset_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14          (k1_zfmisc_1 @ 
% 1.91/2.14           (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)], ['228', '229', '230'])).
% 1.91/2.14  thf('232', plain,
% 1.91/2.14      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.91/2.14         ((v1_xboole_0 @ X37)
% 1.91/2.14          | (v1_xboole_0 @ X40)
% 1.91/2.14          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 1.91/2.14          | ~ (v1_funct_1 @ X39)
% 1.91/2.14          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 1.91/2.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 1.91/2.14          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 1.91/2.14              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 1.91/2.14                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 1.91/2.14          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 1.91/2.14          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 1.91/2.14               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 1.91/2.14          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 1.91/2.14               (k1_zfmisc_1 @ 
% 1.91/2.14                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 1.91/2.14          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 1.91/2.14              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X36) = (
% 1.91/2.14              X38))
% 1.91/2.14          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.91/2.14          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 1.91/2.14          | ~ (v1_funct_1 @ X38)
% 1.91/2.14          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.91/2.14          | (v1_xboole_0 @ X36)
% 1.91/2.14          | (v1_xboole_0 @ X35))),
% 1.91/2.14      inference('simplify', [status(thm)], ['176'])).
% 1.91/2.14  thf('233', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.14         | ~ (v1_funct_1 @ sk_F)
% 1.91/2.14         | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 1.91/2.14         | ~ (m1_subset_1 @ sk_F @ 
% 1.91/2.14              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 1.91/2.14         | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ 
% 1.91/2.14             sk_B_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             sk_D) = (sk_F))
% 1.91/2.14         | ~ (v1_funct_2 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14              (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)
% 1.91/2.14         | ~ (v1_funct_1 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | ((k2_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_E @ 
% 1.91/2.14             (k9_subset_1 @ sk_A @ k1_xboole_0 @ sk_D))
% 1.91/2.14             != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14                 (k9_subset_1 @ sk_A @ k1_xboole_0 @ sk_D)))
% 1.91/2.14         | ~ (m1_subset_1 @ sk_E @ 
% 1.91/2.14              (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))
% 1.91/2.14         | ~ (v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_B_1)
% 1.91/2.14         | ~ (v1_funct_1 @ sk_E)
% 1.91/2.14         | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['231', '232'])).
% 1.91/2.14  thf('234', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('235', plain, ((v1_funct_1 @ sk_F)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('236', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('237', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('238', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.14  thf('239', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('240', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.14  thf('241', plain,
% 1.91/2.14      ((((k3_xboole_0 @ k1_xboole_0 @ sk_D) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['239', '240'])).
% 1.91/2.14  thf('242', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('243', plain,
% 1.91/2.14      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('244', plain,
% 1.91/2.14      (((m1_subset_1 @ sk_E @ 
% 1.91/2.14         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['242', '243'])).
% 1.91/2.14  thf('245', plain,
% 1.91/2.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.91/2.14         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.91/2.14          | ~ (v1_funct_1 @ X31)
% 1.91/2.14          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 1.91/2.14      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.91/2.14  thf('246', plain,
% 1.91/2.14      ((![X0 : $i]:
% 1.91/2.14          (((k2_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_E @ X0)
% 1.91/2.14             = (k7_relat_1 @ sk_E @ X0))
% 1.91/2.14           | ~ (v1_funct_1 @ sk_E)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['244', '245'])).
% 1.91/2.14  thf('247', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('248', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.91/2.14          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('demod', [status(thm)], ['161', '162'])).
% 1.91/2.14  thf('249', plain,
% 1.91/2.14      ((![X0 : $i]:
% 1.91/2.14          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.91/2.14           | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['247', '248'])).
% 1.91/2.14  thf('250', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.91/2.14      inference('simplify', [status(thm)], ['167'])).
% 1.91/2.14  thf('251', plain,
% 1.91/2.14      ((![X0 : $i]: ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)], ['249', '250'])).
% 1.91/2.14  thf('252', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('253', plain,
% 1.91/2.14      ((![X0 : $i]:
% 1.91/2.14          ((k2_partfun1 @ k1_xboole_0 @ sk_B_1 @ sk_E @ X0) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)], ['246', '251', '252'])).
% 1.91/2.14  thf('254', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.91/2.14      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.14  thf('255', plain,
% 1.91/2.14      ((((k3_xboole_0 @ k1_xboole_0 @ sk_D) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['239', '240'])).
% 1.91/2.14  thf('256', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.91/2.14      inference('demod', [status(thm)], ['74', '75'])).
% 1.91/2.14  thf('257', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 1.91/2.14      inference('sup+', [status(thm)], ['77', '105'])).
% 1.91/2.14  thf('258', plain,
% 1.91/2.14      (((m1_subset_1 @ sk_E @ 
% 1.91/2.14         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['242', '243'])).
% 1.91/2.14  thf('259', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('260', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('261', plain,
% 1.91/2.14      (((v1_funct_2 @ sk_E @ k1_xboole_0 @ sk_B_1))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['259', '260'])).
% 1.91/2.14  thf('262', plain, ((v1_funct_1 @ sk_E)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('263', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('264', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('265', plain,
% 1.91/2.14      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup+', [status(thm)], ['263', '264'])).
% 1.91/2.14  thf('266', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ 
% 1.91/2.14             sk_B_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             sk_D) = (sk_F))
% 1.91/2.14         | ~ (v1_funct_2 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14              (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)
% 1.91/2.14         | ~ (v1_funct_1 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | ((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)],
% 1.91/2.14                ['233', '234', '235', '236', '237', '238', '241', '253', 
% 1.91/2.14                 '254', '255', '256', '257', '258', '261', '262', '265'])).
% 1.91/2.14  thf('267', plain,
% 1.91/2.14      (((~ (v1_funct_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | ~ (v1_funct_2 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14              (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)
% 1.91/2.14         | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ 
% 1.91/2.14             sk_B_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             sk_D) = (sk_F))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['266'])).
% 1.91/2.14  thf('268', plain,
% 1.91/2.14      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14          != (sk_F)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('split', [status(esa)], ['113'])).
% 1.91/2.14  thf('269', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('270', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('271', plain,
% 1.91/2.14      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14          != (sk_F)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('demod', [status(thm)], ['268', '269', '270'])).
% 1.91/2.14  thf('272', plain,
% 1.91/2.14      (((~ (v1_funct_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | ~ (v1_funct_2 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14              (k4_subset_1 @ sk_A @ k1_xboole_0 @ sk_D) @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('simplify_reflect-', [status(thm)], ['267', '271'])).
% 1.91/2.14  thf('273', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | ~ (v1_funct_1 @ 
% 1.91/2.14              (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['225', '272'])).
% 1.91/2.14  thf('274', plain,
% 1.91/2.14      (((~ (v1_funct_1 @ 
% 1.91/2.14            (k1_tmap_1 @ sk_A @ sk_B_1 @ k1_xboole_0 @ sk_D @ sk_E @ sk_F))
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['273'])).
% 1.91/2.14  thf('275', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_D)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['219', '274'])).
% 1.91/2.14  thf('276', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_D)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ sk_A)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('simplify', [status(thm)], ['275'])).
% 1.91/2.14  thf('277', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('278', plain,
% 1.91/2.14      ((((v1_xboole_0 @ sk_A)
% 1.91/2.14         | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14         | (v1_xboole_0 @ k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['276', '277'])).
% 1.91/2.14  thf('279', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('280', plain,
% 1.91/2.14      ((((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_B_1)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['278', '279'])).
% 1.91/2.14  thf('281', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0)))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['213', '214'])).
% 1.91/2.14  thf('282', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('283', plain,
% 1.91/2.14      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('sup-', [status(thm)], ['281', '282'])).
% 1.91/2.14  thf('284', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_B_1))
% 1.91/2.14         <= (~
% 1.91/2.14             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14                = (sk_F))))),
% 1.91/2.14      inference('clc', [status(thm)], ['280', '283'])).
% 1.91/2.14  thf('285', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('286', plain,
% 1.91/2.14      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14          = (sk_F)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['284', '285'])).
% 1.91/2.14  thf('287', plain,
% 1.91/2.14      (~
% 1.91/2.14       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14          = (sk_E))) | 
% 1.91/2.14       ~
% 1.91/2.14       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.91/2.14          = (sk_F))) | 
% 1.91/2.14       ~
% 1.91/2.14       (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 1.91/2.14          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 1.91/2.14          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 1.91/2.14             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 1.91/2.14      inference('split', [status(esa)], ['113'])).
% 1.91/2.14  thf('288', plain,
% 1.91/2.14      (~
% 1.91/2.14       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14          = (sk_E)))),
% 1.91/2.14      inference('sat_resolution*', [status(thm)], ['171', '286', '287'])).
% 1.91/2.14  thf('289', plain,
% 1.91/2.14      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 1.91/2.14         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 1.91/2.14         != (sk_E))),
% 1.91/2.14      inference('simpl_trail', [status(thm)], ['114', '288'])).
% 1.91/2.14  thf('290', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ~ (v1_funct_2 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 1.91/2.14             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify_reflect-', [status(thm)], ['112', '289'])).
% 1.91/2.14  thf('291', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | ((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['30', '290'])).
% 1.91/2.14  thf('292', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ~ (v1_funct_1 @ 
% 1.91/2.14             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['291'])).
% 1.91/2.14  thf('293', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | ((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['15', '292'])).
% 1.91/2.14  thf('294', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['293'])).
% 1.91/2.14  thf('295', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 1.91/2.14          | ~ (v1_relat_1 @ X0)
% 1.91/2.14          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('sup+', [status(thm)], ['127', '135'])).
% 1.91/2.14  thf('296', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('simplify', [status(thm)], ['293'])).
% 1.91/2.14  thf('297', plain,
% 1.91/2.14      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.91/2.14        | ~ (v1_relat_1 @ sk_E)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('sup-', [status(thm)], ['295', '296'])).
% 1.91/2.14  thf('298', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 1.91/2.14      inference('demod', [status(thm)], ['148', '151', '154'])).
% 1.91/2.14  thf('299', plain, ((v1_relat_1 @ sk_E)),
% 1.91/2.14      inference('sup-', [status(thm)], ['149', '150'])).
% 1.91/2.14  thf('300', plain,
% 1.91/2.14      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | ((sk_C) = (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('demod', [status(thm)], ['297', '298', '299'])).
% 1.91/2.14  thf('301', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_D)
% 1.91/2.14        | ((sk_C) = (k1_xboole_0)))),
% 1.91/2.14      inference('simplify', [status(thm)], ['300'])).
% 1.91/2.14  thf('302', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('303', plain,
% 1.91/2.14      ((((sk_C) = (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_C)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('sup-', [status(thm)], ['301', '302'])).
% 1.91/2.14  thf('304', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('305', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | ((sk_C) = (k1_xboole_0)))),
% 1.91/2.14      inference('sup-', [status(thm)], ['303', '304'])).
% 1.91/2.14  thf('306', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('307', plain, ((((sk_C) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_1))),
% 1.91/2.14      inference('clc', [status(thm)], ['305', '306'])).
% 1.91/2.14  thf('308', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('309', plain, (((sk_C) = (k1_xboole_0))),
% 1.91/2.14      inference('clc', [status(thm)], ['307', '308'])).
% 1.91/2.14  thf('310', plain,
% 1.91/2.14      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['294', '309'])).
% 1.91/2.14  thf('311', plain,
% 1.91/2.14      (![X0 : $i]:
% 1.91/2.14         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.91/2.14          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 1.91/2.14      inference('demod', [status(thm)], ['161', '162'])).
% 1.91/2.14  thf('312', plain, (((sk_C) = (k1_xboole_0))),
% 1.91/2.14      inference('clc', [status(thm)], ['307', '308'])).
% 1.91/2.14  thf('313', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.91/2.14      inference('simplify', [status(thm)], ['167'])).
% 1.91/2.14  thf('314', plain, (![X0 : $i]: ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0))),
% 1.91/2.14      inference('demod', [status(thm)], ['311', '312', '313'])).
% 1.91/2.14  thf('315', plain,
% 1.91/2.14      ((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.14        | (v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14        | (v1_xboole_0 @ sk_D))),
% 1.91/2.14      inference('demod', [status(thm)], ['310', '314'])).
% 1.91/2.14  thf('316', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_D)
% 1.91/2.14        | (v1_xboole_0 @ k1_xboole_0)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ sk_A))),
% 1.91/2.14      inference('simplify', [status(thm)], ['315'])).
% 1.91/2.14  thf('317', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('318', plain,
% 1.91/2.14      (((v1_xboole_0 @ sk_A)
% 1.91/2.14        | (v1_xboole_0 @ sk_B_1)
% 1.91/2.14        | (v1_xboole_0 @ k1_xboole_0))),
% 1.91/2.14      inference('sup-', [status(thm)], ['316', '317'])).
% 1.91/2.14  thf('319', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('320', plain, (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_B_1))),
% 1.91/2.14      inference('clc', [status(thm)], ['318', '319'])).
% 1.91/2.14  thf('321', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.91/2.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.14  thf('322', plain, (((sk_C) = (k1_xboole_0))),
% 1.91/2.14      inference('clc', [status(thm)], ['307', '308'])).
% 1.91/2.14  thf('323', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.91/2.14      inference('demod', [status(thm)], ['321', '322'])).
% 1.91/2.14  thf('324', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.91/2.14      inference('clc', [status(thm)], ['320', '323'])).
% 1.91/2.14  thf('325', plain, ($false), inference('demod', [status(thm)], ['0', '324'])).
% 1.91/2.14  
% 1.91/2.14  % SZS output end Refutation
% 1.91/2.14  
% 1.91/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
