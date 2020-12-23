%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CgLEhHfBy1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:54 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 738 expanded)
%              Number of leaves         :   37 ( 234 expanded)
%              Depth                    :   30
%              Number of atoms          : 3407 (27995 expanded)
%              Number of equality atoms :  110 ( 913 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ( v1_xboole_0 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X54 ) )
      | ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X52 )
      | ( v1_xboole_0 @ X54 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X54 @ X52 @ X51 @ X53 @ X50 @ X55 ) ) ) ),
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
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ( v1_xboole_0 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X54 ) )
      | ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X52 )
      | ( v1_xboole_0 @ X54 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X54 @ X52 @ X51 @ X53 @ X50 @ X55 ) @ ( k4_subset_1 @ X54 @ X51 @ X53 ) @ X52 ) ) ),
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
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ( v1_xboole_0 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X54 ) )
      | ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X52 )
      | ( v1_xboole_0 @ X54 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X53 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X54 @ X52 @ X51 @ X53 @ X50 @ X55 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X54 @ X51 @ X53 ) @ X52 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ( X49
       != ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 @ X49 @ X48 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 )
      | ~ ( v1_funct_1 @ X49 )
      | ( ( k2_partfun1 @ X48 @ X43 @ X47 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) )
       != ( k2_partfun1 @ X44 @ X43 @ X46 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X43 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X43 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X43 ) ) )
      | ( ( k2_partfun1 @ X48 @ X43 @ X47 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) )
       != ( k2_partfun1 @ X44 @ X43 @ X46 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) @ X48 )
        = X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X43 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_subset_1 @ X26 @ X27 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 )
        = ( k7_relat_1 @ X39 @ X42 ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('73',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['81','84'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k7_relat_1 @ X25 @ X24 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('91',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 )
        = ( k7_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('100',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','88','89','90','95','100','101','102','103','104'])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
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
    inference('sup-',[status(thm)],['30','106'])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('113',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['109'])).

thf('114',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('116',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('120',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','87'])).

thf('121',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('122',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','99'])).

thf('123',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122'])).

thf('124',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('128',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ( X49
       != ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 @ X49 @ X44 )
        = X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 )
      | ~ ( v1_funct_1 @ X49 )
      | ( ( k2_partfun1 @ X48 @ X43 @ X47 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) )
       != ( k2_partfun1 @ X44 @ X43 @ X46 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X43 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X48 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('129',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X43 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X43 ) ) )
      | ( ( k2_partfun1 @ X48 @ X43 @ X47 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) )
       != ( k2_partfun1 @ X44 @ X43 @ X46 @ ( k9_subset_1 @ X45 @ X48 @ X44 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X45 @ X48 @ X44 ) @ X43 @ ( k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46 ) @ X44 )
        = X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
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
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('136',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('138',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','87'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('140',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('142',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','99'])).

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
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137','138','139','140','141','142','143','144','145','146'])).

thf('148',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
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
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['126','148'])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
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
    inference('sup-',[status(thm)],['125','150'])).

thf('152',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['109'])).

thf('154',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['109'])).

thf('165',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['124','163','164'])).

thf('166',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['110','165'])).

thf('167',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['108','166'])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','167'])).

thf('169',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    $false ),
    inference(demod,[status(thm)],['0','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CgLEhHfBy1
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/0.99  % Solved by: fo/fo7.sh
% 0.81/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/0.99  % done 937 iterations in 0.537s
% 0.81/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/0.99  % SZS output start Refutation
% 0.81/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.81/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/0.99  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.81/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.81/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.81/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.81/0.99  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.81/0.99  thf(sk_F_type, type, sk_F: $i).
% 0.81/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.81/0.99  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.81/0.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.81/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.81/0.99  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.81/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.81/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.81/0.99  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.81/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.81/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.81/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.81/0.99  thf(sk_E_type, type, sk_E: $i).
% 0.81/0.99  thf(t6_tmap_1, conjecture,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/0.99       ( ![B:$i]:
% 0.81/0.99         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.81/0.99           ( ![C:$i]:
% 0.81/0.99             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.81/0.99                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/0.99               ( ![D:$i]:
% 0.81/0.99                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.81/0.99                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/0.99                   ( ( r1_subset_1 @ C @ D ) =>
% 0.81/0.99                     ( ![E:$i]:
% 0.81/0.99                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.81/0.99                           ( m1_subset_1 @
% 0.81/0.99                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.81/0.99                         ( ![F:$i]:
% 0.81/0.99                           ( ( ( v1_funct_1 @ F ) & 
% 0.81/0.99                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.81/0.99                               ( m1_subset_1 @
% 0.81/0.99                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.81/0.99                             ( ( ( k2_partfun1 @
% 0.81/0.99                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.81/0.99                                 ( k2_partfun1 @
% 0.81/0.99                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.81/0.99                               ( ( k2_partfun1 @
% 0.81/0.99                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.81/0.99                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.81/0.99                                 ( E ) ) & 
% 0.81/0.99                               ( ( k2_partfun1 @
% 0.81/0.99                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.81/0.99                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.81/0.99                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.81/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.81/0.99    (~( ![A:$i]:
% 0.81/0.99        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/0.99          ( ![B:$i]:
% 0.81/0.99            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.81/0.99              ( ![C:$i]:
% 0.81/0.99                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.81/0.99                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/0.99                  ( ![D:$i]:
% 0.81/0.99                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.81/0.99                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/0.99                      ( ( r1_subset_1 @ C @ D ) =>
% 0.81/0.99                        ( ![E:$i]:
% 0.81/0.99                          ( ( ( v1_funct_1 @ E ) & 
% 0.81/0.99                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.81/0.99                              ( m1_subset_1 @
% 0.81/0.99                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.81/0.99                            ( ![F:$i]:
% 0.81/0.99                              ( ( ( v1_funct_1 @ F ) & 
% 0.81/0.99                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.81/0.99                                  ( m1_subset_1 @
% 0.81/0.99                                    F @ 
% 0.81/0.99                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.81/0.99                                ( ( ( k2_partfun1 @
% 0.81/0.99                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.81/0.99                                    ( k2_partfun1 @
% 0.81/0.99                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.81/0.99                                  ( ( k2_partfun1 @
% 0.81/0.99                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.81/0.99                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.81/0.99                                    ( E ) ) & 
% 0.81/0.99                                  ( ( k2_partfun1 @
% 0.81/0.99                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.81/0.99                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.81/0.99                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.81/0.99    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.81/0.99  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('2', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('3', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf(dt_k1_tmap_1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.81/0.99     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.81/0.99         ( ~( v1_xboole_0 @ C ) ) & 
% 0.81/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.81/0.99         ( ~( v1_xboole_0 @ D ) ) & 
% 0.81/0.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.81/0.99         ( v1_funct_2 @ E @ C @ B ) & 
% 0.81/0.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.81/0.99         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.81/0.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.81/0.99       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.81/0.99         ( v1_funct_2 @
% 0.81/0.99           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.81/0.99           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.81/0.99         ( m1_subset_1 @
% 0.81/0.99           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.81/0.99           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.81/0.99  thf('4', plain,
% 0.81/0.99      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.81/0.99          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 0.81/0.99          | ~ (v1_funct_1 @ X50)
% 0.81/0.99          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 0.81/0.99          | (v1_xboole_0 @ X53)
% 0.81/0.99          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X54))
% 0.81/0.99          | (v1_xboole_0 @ X51)
% 0.81/0.99          | (v1_xboole_0 @ X52)
% 0.81/0.99          | (v1_xboole_0 @ X54)
% 0.81/0.99          | ~ (v1_funct_1 @ X55)
% 0.81/0.99          | ~ (v1_funct_2 @ X55 @ X53 @ X52)
% 0.81/0.99          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.81/0.99          | (v1_funct_1 @ (k1_tmap_1 @ X54 @ X52 @ X51 @ X53 @ X50 @ X55)))),
% 0.81/0.99      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.81/0.99  thf('5', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.81/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.81/0.99          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.81/0.99          | ~ (v1_funct_1 @ X0)
% 0.81/0.99          | (v1_xboole_0 @ X2)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.81/0.99          | (v1_xboole_0 @ X1)
% 0.81/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.81/0.99          | ~ (v1_funct_1 @ sk_E)
% 0.81/0.99          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.81/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.81/0.99  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('8', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.81/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.81/0.99          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.81/0.99          | ~ (v1_funct_1 @ X0)
% 0.81/0.99          | (v1_xboole_0 @ X2)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.81/0.99          | (v1_xboole_0 @ X1)
% 0.81/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.81/0.99      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.81/0.99  thf('9', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_D)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.81/0.99          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.81/0.99          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.81/0.99      inference('sup-', [status(thm)], ['2', '8'])).
% 0.81/0.99  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('12', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_D)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.81/0.99      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.81/0.99  thf('13', plain,
% 0.81/0.99      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['1', '12'])).
% 0.81/0.99  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('15', plain,
% 0.81/0.99      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('demod', [status(thm)], ['13', '14'])).
% 0.81/0.99  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('17', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('18', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('19', plain,
% 0.81/0.99      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.81/0.99          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 0.81/0.99          | ~ (v1_funct_1 @ X50)
% 0.81/0.99          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 0.81/0.99          | (v1_xboole_0 @ X53)
% 0.81/0.99          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X54))
% 0.81/0.99          | (v1_xboole_0 @ X51)
% 0.81/0.99          | (v1_xboole_0 @ X52)
% 0.81/0.99          | (v1_xboole_0 @ X54)
% 0.81/0.99          | ~ (v1_funct_1 @ X55)
% 0.81/0.99          | ~ (v1_funct_2 @ X55 @ X53 @ X52)
% 0.81/0.99          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.81/0.99          | (v1_funct_2 @ (k1_tmap_1 @ X54 @ X52 @ X51 @ X53 @ X50 @ X55) @ 
% 0.81/0.99             (k4_subset_1 @ X54 @ X51 @ X53) @ X52))),
% 0.81/0.99      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.81/0.99  thf('20', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.81/0.99           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.81/0.99          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.81/0.99          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.81/0.99          | ~ (v1_funct_1 @ X2)
% 0.81/0.99          | (v1_xboole_0 @ X1)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.81/0.99          | ~ (v1_funct_1 @ sk_E)
% 0.81/0.99          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.81/0.99      inference('sup-', [status(thm)], ['18', '19'])).
% 0.81/0.99  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('23', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.81/0.99           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.81/0.99          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.81/0.99          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.81/0.99          | ~ (v1_funct_1 @ X2)
% 0.81/0.99          | (v1_xboole_0 @ X1)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.81/0.99      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.81/0.99  thf('24', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_D)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.81/0.99          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.81/0.99          | (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.81/0.99      inference('sup-', [status(thm)], ['17', '23'])).
% 0.81/0.99  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('27', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_D)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.81/0.99      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.81/0.99  thf('28', plain,
% 0.81/0.99      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['16', '27'])).
% 0.81/0.99  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('30', plain,
% 0.81/0.99      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('demod', [status(thm)], ['28', '29'])).
% 0.81/0.99  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('32', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('33', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('34', plain,
% 0.81/0.99      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.81/0.99          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 0.81/0.99          | ~ (v1_funct_1 @ X50)
% 0.81/0.99          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 0.81/0.99          | (v1_xboole_0 @ X53)
% 0.81/0.99          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X54))
% 0.81/0.99          | (v1_xboole_0 @ X51)
% 0.81/0.99          | (v1_xboole_0 @ X52)
% 0.81/0.99          | (v1_xboole_0 @ X54)
% 0.81/0.99          | ~ (v1_funct_1 @ X55)
% 0.81/0.99          | ~ (v1_funct_2 @ X55 @ X53 @ X52)
% 0.81/0.99          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52)))
% 0.81/0.99          | (m1_subset_1 @ (k1_tmap_1 @ X54 @ X52 @ X51 @ X53 @ X50 @ X55) @ 
% 0.81/0.99             (k1_zfmisc_1 @ 
% 0.81/0.99              (k2_zfmisc_1 @ (k4_subset_1 @ X54 @ X51 @ X53) @ X52))))),
% 0.81/0.99      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.81/0.99  thf('35', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.81/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.81/0.99          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.81/0.99          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.81/0.99          | ~ (v1_funct_1 @ X2)
% 0.81/0.99          | (v1_xboole_0 @ X1)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.81/0.99          | ~ (v1_funct_1 @ sk_E)
% 0.81/0.99          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.81/0.99      inference('sup-', [status(thm)], ['33', '34'])).
% 0.81/0.99  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('38', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/0.99         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.81/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.81/0.99          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.81/0.99          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.81/0.99          | ~ (v1_funct_1 @ X2)
% 0.81/0.99          | (v1_xboole_0 @ X1)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.81/0.99      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.81/0.99  thf('39', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_D)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | ~ (v1_funct_1 @ sk_F)
% 0.81/0.99          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.81/0.99          | (m1_subset_1 @ 
% 0.81/0.99             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k1_zfmisc_1 @ 
% 0.81/0.99              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['32', '38'])).
% 0.81/0.99  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('42', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_D)
% 0.81/0.99          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.81/0.99          | (v1_xboole_0 @ sk_C)
% 0.81/0.99          | (v1_xboole_0 @ sk_B)
% 0.81/0.99          | (v1_xboole_0 @ X0)
% 0.81/0.99          | (m1_subset_1 @ 
% 0.81/0.99             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k1_zfmisc_1 @ 
% 0.81/0.99              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.81/0.99      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.81/0.99  thf('43', plain,
% 0.81/0.99      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99         (k1_zfmisc_1 @ 
% 0.81/0.99          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['31', '42'])).
% 0.81/0.99  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('45', plain,
% 0.81/0.99      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99         (k1_zfmisc_1 @ 
% 0.81/0.99          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/0.99  thf(d1_tmap_1, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.81/0.99       ( ![B:$i]:
% 0.81/0.99         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.81/0.99           ( ![C:$i]:
% 0.81/0.99             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.81/0.99                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/0.99               ( ![D:$i]:
% 0.81/0.99                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.81/0.99                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.81/0.99                   ( ![E:$i]:
% 0.81/0.99                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.81/0.99                         ( m1_subset_1 @
% 0.81/0.99                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.81/0.99                       ( ![F:$i]:
% 0.81/0.99                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.81/0.99                             ( m1_subset_1 @
% 0.81/0.99                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.81/0.99                           ( ( ( k2_partfun1 @
% 0.81/0.99                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.81/0.99                               ( k2_partfun1 @
% 0.81/0.99                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.81/0.99                             ( ![G:$i]:
% 0.81/0.99                               ( ( ( v1_funct_1 @ G ) & 
% 0.81/0.99                                   ( v1_funct_2 @
% 0.81/0.99                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.81/0.99                                   ( m1_subset_1 @
% 0.81/0.99                                     G @ 
% 0.81/0.99                                     ( k1_zfmisc_1 @
% 0.81/0.99                                       ( k2_zfmisc_1 @
% 0.81/0.99                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.81/0.99                                 ( ( ( G ) =
% 0.81/0.99                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.81/0.99                                   ( ( ( k2_partfun1 @
% 0.81/0.99                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.81/0.99                                         C ) =
% 0.81/0.99                                       ( E ) ) & 
% 0.81/0.99                                     ( ( k2_partfun1 @
% 0.81/0.99                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.81/0.99                                         D ) =
% 0.81/0.99                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.81/0.99  thf('46', plain,
% 0.81/0.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X43)
% 0.81/0.99          | (v1_xboole_0 @ X44)
% 0.81/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | ~ (v1_funct_1 @ X46)
% 0.81/0.99          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.81/0.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.81/0.99          | ((X49) != (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46))
% 0.81/0.99          | ((k2_partfun1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43 @ X49 @ X48)
% 0.81/0.99              = (X47))
% 0.81/0.99          | ~ (m1_subset_1 @ X49 @ 
% 0.81/0.99               (k1_zfmisc_1 @ 
% 0.81/0.99                (k2_zfmisc_1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43)))
% 0.81/0.99          | ~ (v1_funct_2 @ X49 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43)
% 0.81/0.99          | ~ (v1_funct_1 @ X49)
% 0.81/0.99          | ((k2_partfun1 @ X48 @ X43 @ X47 @ (k9_subset_1 @ X45 @ X48 @ X44))
% 0.81/0.99              != (k2_partfun1 @ X44 @ X43 @ X46 @ 
% 0.81/0.99                  (k9_subset_1 @ X45 @ X48 @ X44)))
% 0.81/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X43)))
% 0.81/0.99          | ~ (v1_funct_2 @ X47 @ X48 @ X43)
% 0.81/0.99          | ~ (v1_funct_1 @ X47)
% 0.81/0.99          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | (v1_xboole_0 @ X48)
% 0.81/0.99          | (v1_xboole_0 @ X45))),
% 0.81/0.99      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.81/0.99  thf('47', plain,
% 0.81/0.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X45)
% 0.81/0.99          | (v1_xboole_0 @ X48)
% 0.81/0.99          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | ~ (v1_funct_1 @ X47)
% 0.81/0.99          | ~ (v1_funct_2 @ X47 @ X48 @ X43)
% 0.81/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X43)))
% 0.81/0.99          | ((k2_partfun1 @ X48 @ X43 @ X47 @ (k9_subset_1 @ X45 @ X48 @ X44))
% 0.81/0.99              != (k2_partfun1 @ X44 @ X43 @ X46 @ 
% 0.81/0.99                  (k9_subset_1 @ X45 @ X48 @ X44)))
% 0.81/0.99          | ~ (v1_funct_1 @ (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46))
% 0.81/0.99          | ~ (v1_funct_2 @ (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46) @ 
% 0.81/0.99               (k4_subset_1 @ X45 @ X48 @ X44) @ X43)
% 0.81/0.99          | ~ (m1_subset_1 @ (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46) @ 
% 0.81/0.99               (k1_zfmisc_1 @ 
% 0.81/0.99                (k2_zfmisc_1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43)))
% 0.81/0.99          | ((k2_partfun1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43 @ 
% 0.81/0.99              (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46) @ X48) = (
% 0.81/0.99              X47))
% 0.81/0.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.81/0.99          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.81/0.99          | ~ (v1_funct_1 @ X46)
% 0.81/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | (v1_xboole_0 @ X44)
% 0.81/0.99          | (v1_xboole_0 @ X43))),
% 0.81/0.99      inference('simplify', [status(thm)], ['46'])).
% 0.81/0.99  thf('48', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | ~ (v1_funct_1 @ sk_F)
% 0.81/0.99        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99            = (sk_E))
% 0.81/0.99        | ~ (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.81/0.99        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.81/0.99        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.81/0.99        | ~ (v1_funct_1 @ sk_E)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['45', '47'])).
% 0.81/0.99  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('52', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf(redefinition_k9_subset_1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i]:
% 0.81/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.81/0.99       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.81/0.99  thf('54', plain,
% 0.81/0.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.81/0.99         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.81/0.99          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.81/0.99      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.81/0.99  thf('55', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/0.99  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf(redefinition_r1_subset_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.81/0.99       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.81/0.99  thf('57', plain,
% 0.81/0.99      (![X26 : $i, X27 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X26)
% 0.81/0.99          | (v1_xboole_0 @ X27)
% 0.81/0.99          | (r1_xboole_0 @ X26 @ X27)
% 0.81/0.99          | ~ (r1_subset_1 @ X26 @ X27))),
% 0.81/0.99      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.81/0.99  thf('58', plain,
% 0.81/0.99      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C))),
% 0.81/0.99      inference('sup-', [status(thm)], ['56', '57'])).
% 0.81/0.99  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.81/0.99      inference('clc', [status(thm)], ['58', '59'])).
% 0.81/0.99  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.81/0.99      inference('clc', [status(thm)], ['60', '61'])).
% 0.81/0.99  thf(d7_xboole_0, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.81/0.99       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.81/0.99  thf('63', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.81/0.99      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.81/0.99  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/0.99  thf('65', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf(redefinition_k2_partfun1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/0.99     ( ( ( v1_funct_1 @ C ) & 
% 0.81/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/0.99       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.81/0.99  thf('66', plain,
% 0.81/0.99      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.81/0.99          | ~ (v1_funct_1 @ X39)
% 0.81/0.99          | ((k2_partfun1 @ X40 @ X41 @ X39 @ X42) = (k7_relat_1 @ X39 @ X42)))),
% 0.81/0.99      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.81/0.99  thf('67', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.81/0.99          | ~ (v1_funct_1 @ sk_E))),
% 0.81/0.99      inference('sup-', [status(thm)], ['65', '66'])).
% 0.81/0.99  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('69', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.81/0.99      inference('demod', [status(thm)], ['67', '68'])).
% 0.81/0.99  thf('70', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf(cc1_relset_1, axiom,
% 0.81/0.99    (![A:$i,B:$i,C:$i]:
% 0.81/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/0.99       ( v1_relat_1 @ C ) ))).
% 0.81/0.99  thf('71', plain,
% 0.81/0.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.81/0.99         ((v1_relat_1 @ X28)
% 0.81/0.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.81/0.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.81/0.99  thf('72', plain, ((v1_relat_1 @ sk_E)),
% 0.81/0.99      inference('sup-', [status(thm)], ['70', '71'])).
% 0.81/0.99  thf(t79_xboole_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.81/0.99  thf('73', plain,
% 0.81/0.99      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.81/0.99      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.81/0.99  thf(symmetry_r1_xboole_0, axiom,
% 0.81/0.99    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.81/0.99  thf('74', plain,
% 0.81/0.99      (![X3 : $i, X4 : $i]:
% 0.81/0.99         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.81/0.99      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.81/0.99  thf('75', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['73', '74'])).
% 0.81/0.99  thf('76', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.81/0.99      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.81/0.99  thf('77', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['75', '76'])).
% 0.81/0.99  thf(t48_xboole_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.81/0.99  thf('78', plain,
% 0.81/0.99      (![X5 : $i, X6 : $i]:
% 0.81/0.99         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.81/0.99           = (k3_xboole_0 @ X5 @ X6))),
% 0.81/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.81/0.99  thf('79', plain,
% 0.81/0.99      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.81/0.99      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.81/0.99  thf('80', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.81/0.99      inference('sup+', [status(thm)], ['78', '79'])).
% 0.81/0.99  thf('81', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.81/0.99          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.81/0.99      inference('sup+', [status(thm)], ['77', '80'])).
% 0.81/0.99  thf('82', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['73', '74'])).
% 0.81/0.99  thf(t83_xboole_1, axiom,
% 0.81/0.99    (![A:$i,B:$i]:
% 0.81/0.99     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.81/0.99  thf('83', plain,
% 0.81/0.99      (![X9 : $i, X10 : $i]:
% 0.81/0.99         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.81/0.99      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.81/0.99  thf('84', plain,
% 0.81/0.99      (![X0 : $i, X1 : $i]:
% 0.81/0.99         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['82', '83'])).
% 0.81/0.99  thf('85', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.81/0.99      inference('demod', [status(thm)], ['81', '84'])).
% 0.81/0.99  thf(t187_relat_1, axiom,
% 0.81/0.99    (![A:$i]:
% 0.81/0.99     ( ( v1_relat_1 @ A ) =>
% 0.81/0.99       ( ![B:$i]:
% 0.81/0.99         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.81/0.99           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.81/0.99  thf('86', plain,
% 0.81/0.99      (![X24 : $i, X25 : $i]:
% 0.81/0.99         (~ (r1_xboole_0 @ X24 @ (k1_relat_1 @ X25))
% 0.81/0.99          | ((k7_relat_1 @ X25 @ X24) = (k1_xboole_0))
% 0.81/0.99          | ~ (v1_relat_1 @ X25))),
% 0.81/0.99      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.81/0.99  thf('87', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (v1_relat_1 @ X0)
% 0.81/0.99          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.81/0.99      inference('sup-', [status(thm)], ['85', '86'])).
% 0.81/0.99  thf('88', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['72', '87'])).
% 0.81/0.99  thf('89', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/0.99  thf('90', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/0.99  thf('91', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('92', plain,
% 0.81/0.99      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.81/0.99         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.81/0.99          | ~ (v1_funct_1 @ X39)
% 0.81/0.99          | ((k2_partfun1 @ X40 @ X41 @ X39 @ X42) = (k7_relat_1 @ X39 @ X42)))),
% 0.81/0.99      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.81/0.99  thf('93', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.81/0.99          | ~ (v1_funct_1 @ sk_F))),
% 0.81/0.99      inference('sup-', [status(thm)], ['91', '92'])).
% 0.81/0.99  thf('94', plain, ((v1_funct_1 @ sk_F)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('95', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.81/0.99      inference('demod', [status(thm)], ['93', '94'])).
% 0.81/0.99  thf('96', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('97', plain,
% 0.81/0.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.81/0.99         ((v1_relat_1 @ X28)
% 0.81/0.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.81/0.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.81/0.99  thf('98', plain, ((v1_relat_1 @ sk_F)),
% 0.81/0.99      inference('sup-', [status(thm)], ['96', '97'])).
% 0.81/0.99  thf('99', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         (~ (v1_relat_1 @ X0)
% 0.81/0.99          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.81/0.99      inference('sup-', [status(thm)], ['85', '86'])).
% 0.81/0.99  thf('100', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['98', '99'])).
% 0.81/0.99  thf('101', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('102', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('103', plain, ((v1_funct_1 @ sk_E)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('104', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('105', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99            = (sk_E))
% 0.81/0.99        | ~ (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ((k1_xboole_0) != (k1_xboole_0))
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_A))),
% 0.81/0.99      inference('demod', [status(thm)],
% 0.81/0.99                ['48', '49', '50', '51', '52', '55', '64', '69', '88', '89', 
% 0.81/0.99                 '90', '95', '100', '101', '102', '103', '104'])).
% 0.81/0.99  thf('106', plain,
% 0.81/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ~ (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99            = (sk_E))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('simplify', [status(thm)], ['105'])).
% 0.81/0.99  thf('107', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99            = (sk_E))
% 0.81/0.99        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.81/0.99      inference('sup-', [status(thm)], ['30', '106'])).
% 0.81/0.99  thf('108', plain,
% 0.81/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99            = (sk_E))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('simplify', [status(thm)], ['107'])).
% 0.81/0.99  thf('109', plain,
% 0.81/0.99      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99            != (sk_E))
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/0.99            != (sk_F)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('110', plain,
% 0.81/0.99      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99          != (sk_E)))
% 0.81/0.99         <= (~
% 0.81/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/0.99                = (sk_E))))),
% 0.81/0.99      inference('split', [status(esa)], ['109'])).
% 0.81/0.99  thf('111', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.81/0.99      inference('demod', [status(thm)], ['93', '94'])).
% 0.81/0.99  thf('112', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/0.99  thf('113', plain,
% 0.81/0.99      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.81/0.99         <= (~
% 0.81/0.99             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.81/0.99      inference('split', [status(esa)], ['109'])).
% 0.81/0.99  thf('114', plain,
% 0.81/0.99      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.81/0.99         <= (~
% 0.81/0.99             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['112', '113'])).
% 0.81/0.99  thf('115', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/0.99  thf('116', plain,
% 0.81/0.99      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.81/0.99          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.81/0.99         <= (~
% 0.81/0.99             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.81/0.99      inference('demod', [status(thm)], ['114', '115'])).
% 0.81/0.99  thf('117', plain,
% 0.81/0.99      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.81/0.99          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.81/0.99         <= (~
% 0.81/0.99             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.81/0.99      inference('sup-', [status(thm)], ['111', '116'])).
% 0.81/0.99  thf('118', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/0.99  thf('119', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.81/0.99      inference('demod', [status(thm)], ['67', '68'])).
% 0.81/0.99  thf('120', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['72', '87'])).
% 0.81/0.99  thf('121', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/0.99  thf('122', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['98', '99'])).
% 0.81/0.99  thf('123', plain,
% 0.81/0.99      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.81/0.99         <= (~
% 0.81/0.99             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.81/0.99      inference('demod', [status(thm)],
% 0.81/0.99                ['117', '118', '119', '120', '121', '122'])).
% 0.81/0.99  thf('124', plain,
% 0.81/0.99      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.81/0.99      inference('simplify', [status(thm)], ['123'])).
% 0.81/0.99  thf('125', plain,
% 0.81/0.99      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('demod', [status(thm)], ['13', '14'])).
% 0.81/0.99  thf('126', plain,
% 0.81/0.99      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('demod', [status(thm)], ['28', '29'])).
% 0.81/0.99  thf('127', plain,
% 0.81/0.99      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99         (k1_zfmisc_1 @ 
% 0.81/0.99          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('demod', [status(thm)], ['43', '44'])).
% 0.81/0.99  thf('128', plain,
% 0.81/0.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X43)
% 0.81/0.99          | (v1_xboole_0 @ X44)
% 0.81/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | ~ (v1_funct_1 @ X46)
% 0.81/0.99          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.81/0.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.81/0.99          | ((X49) != (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46))
% 0.81/0.99          | ((k2_partfun1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43 @ X49 @ X44)
% 0.81/0.99              = (X46))
% 0.81/0.99          | ~ (m1_subset_1 @ X49 @ 
% 0.81/0.99               (k1_zfmisc_1 @ 
% 0.81/0.99                (k2_zfmisc_1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43)))
% 0.81/0.99          | ~ (v1_funct_2 @ X49 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43)
% 0.81/0.99          | ~ (v1_funct_1 @ X49)
% 0.81/0.99          | ((k2_partfun1 @ X48 @ X43 @ X47 @ (k9_subset_1 @ X45 @ X48 @ X44))
% 0.81/0.99              != (k2_partfun1 @ X44 @ X43 @ X46 @ 
% 0.81/0.99                  (k9_subset_1 @ X45 @ X48 @ X44)))
% 0.81/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X43)))
% 0.81/0.99          | ~ (v1_funct_2 @ X47 @ X48 @ X43)
% 0.81/0.99          | ~ (v1_funct_1 @ X47)
% 0.81/0.99          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | (v1_xboole_0 @ X48)
% 0.81/0.99          | (v1_xboole_0 @ X45))),
% 0.81/0.99      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.81/0.99  thf('129', plain,
% 0.81/0.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.81/0.99         ((v1_xboole_0 @ X45)
% 0.81/0.99          | (v1_xboole_0 @ X48)
% 0.81/0.99          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | ~ (v1_funct_1 @ X47)
% 0.81/0.99          | ~ (v1_funct_2 @ X47 @ X48 @ X43)
% 0.81/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X43)))
% 0.81/0.99          | ((k2_partfun1 @ X48 @ X43 @ X47 @ (k9_subset_1 @ X45 @ X48 @ X44))
% 0.81/0.99              != (k2_partfun1 @ X44 @ X43 @ X46 @ 
% 0.81/0.99                  (k9_subset_1 @ X45 @ X48 @ X44)))
% 0.81/0.99          | ~ (v1_funct_1 @ (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46))
% 0.81/0.99          | ~ (v1_funct_2 @ (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46) @ 
% 0.81/0.99               (k4_subset_1 @ X45 @ X48 @ X44) @ X43)
% 0.81/0.99          | ~ (m1_subset_1 @ (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46) @ 
% 0.81/0.99               (k1_zfmisc_1 @ 
% 0.81/0.99                (k2_zfmisc_1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43)))
% 0.81/0.99          | ((k2_partfun1 @ (k4_subset_1 @ X45 @ X48 @ X44) @ X43 @ 
% 0.81/0.99              (k1_tmap_1 @ X45 @ X43 @ X48 @ X44 @ X47 @ X46) @ X44) = (
% 0.81/0.99              X46))
% 0.81/0.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.81/0.99          | ~ (v1_funct_2 @ X46 @ X44 @ X43)
% 0.81/0.99          | ~ (v1_funct_1 @ X46)
% 0.81/0.99          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.81/0.99          | (v1_xboole_0 @ X44)
% 0.81/0.99          | (v1_xboole_0 @ X43))),
% 0.81/0.99      inference('simplify', [status(thm)], ['128'])).
% 0.81/0.99  thf('130', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | ~ (v1_funct_1 @ sk_F)
% 0.81/0.99        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/0.99            = (sk_F))
% 0.81/0.99        | ~ (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.81/0.99            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/0.99            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.81/0.99        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.81/0.99        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.81/0.99        | ~ (v1_funct_1 @ sk_E)
% 0.81/0.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_A))),
% 0.81/0.99      inference('sup-', [status(thm)], ['127', '129'])).
% 0.81/0.99  thf('131', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('132', plain, ((v1_funct_1 @ sk_F)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('133', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('134', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('135', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/0.99  thf('136', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/0.99  thf('137', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.81/0.99      inference('demod', [status(thm)], ['67', '68'])).
% 0.81/0.99  thf('138', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['72', '87'])).
% 0.81/0.99  thf('139', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.81/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/0.99  thf('140', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.81/0.99  thf('141', plain,
% 0.81/0.99      (![X0 : $i]:
% 0.81/0.99         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.81/0.99      inference('demod', [status(thm)], ['93', '94'])).
% 0.81/0.99  thf('142', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/0.99      inference('sup-', [status(thm)], ['98', '99'])).
% 0.81/0.99  thf('143', plain,
% 0.81/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('144', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('145', plain, ((v1_funct_1 @ sk_E)),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('146', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.81/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/0.99  thf('147', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/0.99            = (sk_F))
% 0.81/0.99        | ~ (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ((k1_xboole_0) != (k1_xboole_0))
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_A))),
% 0.81/0.99      inference('demod', [status(thm)],
% 0.81/0.99                ['130', '131', '132', '133', '134', '135', '136', '137', 
% 0.81/0.99                 '138', '139', '140', '141', '142', '143', '144', '145', '146'])).
% 0.81/0.99  thf('148', plain,
% 0.81/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ~ (v1_funct_2 @ 
% 0.81/0.99             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.81/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/0.99            = (sk_F))
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_D))),
% 0.81/0.99      inference('simplify', [status(thm)], ['147'])).
% 0.81/0.99  thf('149', plain,
% 0.81/0.99      (((v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | (v1_xboole_0 @ sk_D)
% 0.81/0.99        | (v1_xboole_0 @ sk_C)
% 0.81/0.99        | (v1_xboole_0 @ sk_B)
% 0.81/0.99        | (v1_xboole_0 @ sk_A)
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/0.99            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/0.99            = (sk_F))
% 0.81/0.99        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.81/0.99      inference('sup-', [status(thm)], ['126', '148'])).
% 0.81/0.99  thf('150', plain,
% 0.81/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00            = (sk_F))
% 0.81/1.00        | (v1_xboole_0 @ sk_A)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_D))),
% 0.81/1.00      inference('simplify', [status(thm)], ['149'])).
% 0.81/1.00  thf('151', plain,
% 0.81/1.00      (((v1_xboole_0 @ sk_D)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_A)
% 0.81/1.00        | (v1_xboole_0 @ sk_D)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_A)
% 0.81/1.00        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00            = (sk_F)))),
% 0.81/1.00      inference('sup-', [status(thm)], ['125', '150'])).
% 0.81/1.00  thf('152', plain,
% 0.81/1.00      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00          = (sk_F))
% 0.81/1.00        | (v1_xboole_0 @ sk_A)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_D))),
% 0.81/1.00      inference('simplify', [status(thm)], ['151'])).
% 0.81/1.00  thf('153', plain,
% 0.81/1.00      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00          != (sk_F)))
% 0.81/1.00         <= (~
% 0.81/1.00             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00                = (sk_F))))),
% 0.81/1.00      inference('split', [status(esa)], ['109'])).
% 0.81/1.00  thf('154', plain,
% 0.81/1.00      (((((sk_F) != (sk_F))
% 0.81/1.00         | (v1_xboole_0 @ sk_D)
% 0.81/1.00         | (v1_xboole_0 @ sk_C)
% 0.81/1.00         | (v1_xboole_0 @ sk_B)
% 0.81/1.00         | (v1_xboole_0 @ sk_A)))
% 0.81/1.00         <= (~
% 0.81/1.00             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00                = (sk_F))))),
% 0.81/1.00      inference('sup-', [status(thm)], ['152', '153'])).
% 0.81/1.00  thf('155', plain,
% 0.81/1.00      ((((v1_xboole_0 @ sk_A)
% 0.81/1.00         | (v1_xboole_0 @ sk_B)
% 0.81/1.00         | (v1_xboole_0 @ sk_C)
% 0.81/1.00         | (v1_xboole_0 @ sk_D)))
% 0.81/1.00         <= (~
% 0.81/1.00             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00                = (sk_F))))),
% 0.81/1.00      inference('simplify', [status(thm)], ['154'])).
% 0.81/1.00  thf('156', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('157', plain,
% 0.81/1.00      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.81/1.00         <= (~
% 0.81/1.00             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00                = (sk_F))))),
% 0.81/1.00      inference('sup-', [status(thm)], ['155', '156'])).
% 0.81/1.00  thf('158', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('159', plain,
% 0.81/1.00      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.81/1.00         <= (~
% 0.81/1.00             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00                = (sk_F))))),
% 0.81/1.00      inference('clc', [status(thm)], ['157', '158'])).
% 0.81/1.00  thf('160', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('161', plain,
% 0.81/1.00      (((v1_xboole_0 @ sk_B))
% 0.81/1.00         <= (~
% 0.81/1.00             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00                = (sk_F))))),
% 0.81/1.00      inference('clc', [status(thm)], ['159', '160'])).
% 0.81/1.00  thf('162', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('163', plain,
% 0.81/1.00      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00          = (sk_F)))),
% 0.81/1.00      inference('sup-', [status(thm)], ['161', '162'])).
% 0.81/1.00  thf('164', plain,
% 0.81/1.00      (~
% 0.81/1.00       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/1.00          = (sk_E))) | 
% 0.81/1.00       ~
% 0.81/1.00       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.81/1.00          = (sk_F))) | 
% 0.81/1.00       ~
% 0.81/1.00       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.81/1.00          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.81/1.00             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.81/1.00      inference('split', [status(esa)], ['109'])).
% 0.81/1.00  thf('165', plain,
% 0.81/1.00      (~
% 0.81/1.00       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/1.00          = (sk_E)))),
% 0.81/1.00      inference('sat_resolution*', [status(thm)], ['124', '163', '164'])).
% 0.81/1.00  thf('166', plain,
% 0.81/1.00      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.81/1.00         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.81/1.00         != (sk_E))),
% 0.81/1.00      inference('simpl_trail', [status(thm)], ['110', '165'])).
% 0.81/1.00  thf('167', plain,
% 0.81/1.00      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.81/1.00        | (v1_xboole_0 @ sk_A)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_D))),
% 0.81/1.00      inference('simplify_reflect-', [status(thm)], ['108', '166'])).
% 0.81/1.00  thf('168', plain,
% 0.81/1.00      (((v1_xboole_0 @ sk_D)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_A)
% 0.81/1.00        | (v1_xboole_0 @ sk_D)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_A))),
% 0.81/1.00      inference('sup-', [status(thm)], ['15', '167'])).
% 0.81/1.00  thf('169', plain,
% 0.81/1.00      (((v1_xboole_0 @ sk_A)
% 0.81/1.00        | (v1_xboole_0 @ sk_B)
% 0.81/1.00        | (v1_xboole_0 @ sk_C)
% 0.81/1.00        | (v1_xboole_0 @ sk_D))),
% 0.81/1.00      inference('simplify', [status(thm)], ['168'])).
% 0.81/1.00  thf('170', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('171', plain,
% 0.81/1.00      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.81/1.00      inference('sup-', [status(thm)], ['169', '170'])).
% 0.81/1.00  thf('172', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('173', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.81/1.00      inference('clc', [status(thm)], ['171', '172'])).
% 0.81/1.00  thf('174', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.81/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.00  thf('175', plain, ((v1_xboole_0 @ sk_B)),
% 0.81/1.00      inference('clc', [status(thm)], ['173', '174'])).
% 0.81/1.00  thf('176', plain, ($false), inference('demod', [status(thm)], ['0', '175'])).
% 0.81/1.00  
% 0.81/1.00  % SZS output end Refutation
% 0.81/1.00  
% 0.81/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
