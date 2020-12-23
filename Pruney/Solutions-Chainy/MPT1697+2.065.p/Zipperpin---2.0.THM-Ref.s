%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PLTHDx4rR5

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:03 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 738 expanded)
%              Number of leaves         :   36 ( 228 expanded)
%              Depth                    :   30
%              Number of atoms          : 3450 (30125 expanded)
%              Number of equality atoms :  116 ( 997 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36 ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36 ) @ ( k4_subset_1 @ X35 @ X32 @ X34 ) @ X33 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X35 @ X32 @ X34 ) @ X33 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ( X30
       != ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ X30 @ X29 )
        = X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ X29 )
        = X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_subset_1 @ X12 @ X13 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['74','77'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('80',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X7 ) @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('87',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('90',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('102',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('105',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['100','101'])).

thf('107',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','87','88','89','94','107','108','109','110','111'])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
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
    inference('sup-',[status(thm)],['30','113'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('120',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['116'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('123',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('127',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('129',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('130',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128','129'])).

thf('131',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('133',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('135',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ( X30
       != ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ X30 @ X25 )
        = X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('136',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ X25 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
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
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('143',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('145',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('147',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('149',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

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
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143','144','145','146','147','148','149','150','151','152','153'])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
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
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['133','155'])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
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
    inference('sup-',[status(thm)],['132','157'])).

thf('159',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['116'])).

thf('161',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['116'])).

thf('172',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['131','170','171'])).

thf('173',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['117','172'])).

thf('174',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['115','173'])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','174'])).

thf('176',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['0','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PLTHDx4rR5
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:36:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 172 iterations in 0.243s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(sk_E_type, type, sk_E: $i).
% 0.54/0.75  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.54/0.75  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.75  thf(sk_F_type, type, sk_F: $i).
% 0.54/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.75  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.75  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(t6_tmap_1, conjecture,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.75           ( ![C:$i]:
% 0.54/0.75             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.54/0.75                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.75               ( ![D:$i]:
% 0.54/0.75                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.54/0.75                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.75                   ( ( r1_subset_1 @ C @ D ) =>
% 0.54/0.75                     ( ![E:$i]:
% 0.54/0.75                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.54/0.75                           ( m1_subset_1 @
% 0.54/0.75                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.54/0.75                         ( ![F:$i]:
% 0.54/0.75                           ( ( ( v1_funct_1 @ F ) & 
% 0.54/0.75                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.54/0.75                               ( m1_subset_1 @
% 0.54/0.75                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.54/0.75                             ( ( ( k2_partfun1 @
% 0.54/0.75                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.54/0.75                                 ( k2_partfun1 @
% 0.54/0.75                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.54/0.75                               ( ( k2_partfun1 @
% 0.54/0.75                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.54/0.75                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.54/0.75                                 ( E ) ) & 
% 0.54/0.75                               ( ( k2_partfun1 @
% 0.54/0.75                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.54/0.75                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.54/0.75                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i]:
% 0.54/0.75        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.75          ( ![B:$i]:
% 0.54/0.75            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.75              ( ![C:$i]:
% 0.54/0.75                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.54/0.75                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.75                  ( ![D:$i]:
% 0.54/0.75                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.54/0.75                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.75                      ( ( r1_subset_1 @ C @ D ) =>
% 0.54/0.75                        ( ![E:$i]:
% 0.54/0.75                          ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.75                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.54/0.75                              ( m1_subset_1 @
% 0.54/0.75                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.54/0.75                            ( ![F:$i]:
% 0.54/0.75                              ( ( ( v1_funct_1 @ F ) & 
% 0.54/0.75                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.54/0.75                                  ( m1_subset_1 @
% 0.54/0.75                                    F @ 
% 0.54/0.75                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.54/0.75                                ( ( ( k2_partfun1 @
% 0.54/0.75                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.54/0.75                                    ( k2_partfun1 @
% 0.54/0.75                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.54/0.75                                  ( ( k2_partfun1 @
% 0.54/0.75                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.54/0.75                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.54/0.75                                    ( E ) ) & 
% 0.54/0.75                                  ( ( k2_partfun1 @
% 0.54/0.75                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.54/0.75                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.54/0.75                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.54/0.75  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(dt_k1_tmap_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.75     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.54/0.75         ( ~( v1_xboole_0 @ C ) ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.54/0.75         ( ~( v1_xboole_0 @ D ) ) & 
% 0.54/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.54/0.75         ( v1_funct_2 @ E @ C @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.54/0.75         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.54/0.75       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.54/0.75         ( v1_funct_2 @
% 0.54/0.75           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.54/0.75           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.54/0.75         ( m1_subset_1 @
% 0.54/0.75           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.54/0.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.54/0.75          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.54/0.75          | ~ (v1_funct_1 @ X31)
% 0.54/0.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.54/0.75          | (v1_xboole_0 @ X34)
% 0.54/0.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.54/0.75          | (v1_xboole_0 @ X32)
% 0.54/0.75          | (v1_xboole_0 @ X33)
% 0.54/0.75          | (v1_xboole_0 @ X35)
% 0.54/0.75          | ~ (v1_funct_1 @ X36)
% 0.54/0.75          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.54/0.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.54/0.75          | (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36)))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.54/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.54/0.75          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | (v1_xboole_0 @ X2)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.54/0.75          | (v1_xboole_0 @ X1)
% 0.54/0.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.54/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.75  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.54/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.54/0.75          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.54/0.75          | ~ (v1_funct_1 @ X0)
% 0.54/0.75          | (v1_xboole_0 @ X2)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.54/0.75          | (v1_xboole_0 @ X1)
% 0.54/0.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.54/0.75      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_D)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ sk_F)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.54/0.75          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['2', '8'])).
% 0.54/0.75  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_D)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.54/0.75      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '12'])).
% 0.54/0.75  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.54/0.75          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.54/0.75          | ~ (v1_funct_1 @ X31)
% 0.54/0.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.54/0.75          | (v1_xboole_0 @ X34)
% 0.54/0.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.54/0.75          | (v1_xboole_0 @ X32)
% 0.54/0.75          | (v1_xboole_0 @ X33)
% 0.54/0.75          | (v1_xboole_0 @ X35)
% 0.54/0.75          | ~ (v1_funct_1 @ X36)
% 0.54/0.75          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.54/0.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.54/0.75          | (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36) @ 
% 0.54/0.75             (k4_subset_1 @ X35 @ X32 @ X34) @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.54/0.75           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.54/0.75          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.54/0.75          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.54/0.75          | ~ (v1_funct_1 @ X2)
% 0.54/0.75          | (v1_xboole_0 @ X1)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.75  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.54/0.75           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.54/0.75          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.54/0.75          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.54/0.75          | ~ (v1_funct_1 @ X2)
% 0.54/0.75          | (v1_xboole_0 @ X1)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.54/0.75      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_D)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ sk_F)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.54/0.75          | (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['17', '23'])).
% 0.54/0.75  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_D)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['16', '27'])).
% 0.54/0.75  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.75  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.54/0.75          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.54/0.75          | ~ (v1_funct_1 @ X31)
% 0.54/0.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.54/0.75          | (v1_xboole_0 @ X34)
% 0.54/0.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.54/0.75          | (v1_xboole_0 @ X32)
% 0.54/0.75          | (v1_xboole_0 @ X33)
% 0.54/0.75          | (v1_xboole_0 @ X35)
% 0.54/0.75          | ~ (v1_funct_1 @ X36)
% 0.54/0.75          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.54/0.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.54/0.75          | (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36) @ 
% 0.54/0.75             (k1_zfmisc_1 @ 
% 0.54/0.75              (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X32 @ X34) @ X33))))),
% 0.54/0.75      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.54/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.54/0.75          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.54/0.75          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.54/0.75          | ~ (v1_funct_1 @ X2)
% 0.54/0.75          | (v1_xboole_0 @ X1)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.75  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.54/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.54/0.75          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.54/0.75          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.54/0.75          | ~ (v1_funct_1 @ X2)
% 0.54/0.75          | (v1_xboole_0 @ X1)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.54/0.75      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_D)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (v1_funct_1 @ sk_F)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.54/0.75          | (m1_subset_1 @ 
% 0.54/0.75             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k1_zfmisc_1 @ 
% 0.54/0.75              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['32', '38'])).
% 0.54/0.75  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_D)
% 0.54/0.75          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.54/0.75          | (v1_xboole_0 @ sk_C)
% 0.54/0.75          | (v1_xboole_0 @ sk_B)
% 0.54/0.75          | (v1_xboole_0 @ X0)
% 0.54/0.75          | (m1_subset_1 @ 
% 0.54/0.75             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k1_zfmisc_1 @ 
% 0.54/0.75              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.54/0.75      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['31', '42'])).
% 0.54/0.75  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.75  thf(d1_tmap_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.75           ( ![C:$i]:
% 0.54/0.75             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.54/0.75                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.75               ( ![D:$i]:
% 0.54/0.75                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.54/0.75                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.75                   ( ![E:$i]:
% 0.54/0.75                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.54/0.75                         ( m1_subset_1 @
% 0.54/0.75                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.54/0.75                       ( ![F:$i]:
% 0.54/0.75                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.54/0.75                             ( m1_subset_1 @
% 0.54/0.75                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.54/0.75                           ( ( ( k2_partfun1 @
% 0.54/0.75                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.54/0.75                               ( k2_partfun1 @
% 0.54/0.75                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.54/0.75                             ( ![G:$i]:
% 0.54/0.75                               ( ( ( v1_funct_1 @ G ) & 
% 0.54/0.75                                   ( v1_funct_2 @
% 0.54/0.75                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.54/0.75                                   ( m1_subset_1 @
% 0.54/0.75                                     G @ 
% 0.54/0.75                                     ( k1_zfmisc_1 @
% 0.54/0.75                                       ( k2_zfmisc_1 @
% 0.54/0.75                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.54/0.75                                 ( ( ( G ) =
% 0.54/0.75                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.54/0.75                                   ( ( ( k2_partfun1 @
% 0.54/0.75                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.54/0.75                                         C ) =
% 0.54/0.75                                       ( E ) ) & 
% 0.54/0.75                                     ( ( k2_partfun1 @
% 0.54/0.75                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.54/0.75                                         D ) =
% 0.54/0.75                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.75         ((v1_xboole_0 @ X24)
% 0.54/0.75          | (v1_xboole_0 @ X25)
% 0.54/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | ~ (v1_funct_1 @ X27)
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.54/0.75          | ((X30) != (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.54/0.75          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ X30 @ X29)
% 0.54/0.75              = (X28))
% 0.54/0.75          | ~ (m1_subset_1 @ X30 @ 
% 0.54/0.75               (k1_zfmisc_1 @ 
% 0.54/0.75                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X30 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X30)
% 0.54/0.75          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.54/0.75              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.54/0.75                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.54/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | (v1_xboole_0 @ X29)
% 0.54/0.75          | (v1_xboole_0 @ X26))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.75         ((v1_xboole_0 @ X26)
% 0.54/0.75          | (v1_xboole_0 @ X29)
% 0.54/0.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.54/0.75          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.54/0.75              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.54/0.75                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.54/0.75          | ~ (v1_funct_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.54/0.75          | ~ (v1_funct_2 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.54/0.75               (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.54/0.75               (k1_zfmisc_1 @ 
% 0.54/0.75                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.54/0.75          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ 
% 0.54/0.75              (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ X29) = (
% 0.54/0.75              X28))
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X27)
% 0.54/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | (v1_xboole_0 @ X25)
% 0.54/0.75          | (v1_xboole_0 @ X24))),
% 0.54/0.75      inference('simplify', [status(thm)], ['46'])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_F)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75            = (sk_E))
% 0.54/0.75        | ~ (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.54/0.75        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.54/0.75        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_E)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['45', '47'])).
% 0.54/0.75  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_k9_subset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.75       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.75         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.54/0.75          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_r1_subset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.54/0.75       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      (![X12 : $i, X13 : $i]:
% 0.54/0.75         ((v1_xboole_0 @ X12)
% 0.54/0.75          | (v1_xboole_0 @ X13)
% 0.54/0.75          | (r1_xboole_0 @ X12 @ X13)
% 0.54/0.75          | ~ (r1_subset_1 @ X12 @ X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.75  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.54/0.75      inference('clc', [status(thm)], ['58', '59'])).
% 0.54/0.75  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.54/0.75      inference('clc', [status(thm)], ['60', '61'])).
% 0.54/0.75  thf(d7_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.54/0.75       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.75  thf('63', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.75  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_k2_partfun1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.54/0.75          | ~ (v1_funct_1 @ X20)
% 0.54/0.75          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ sk_E))),
% 0.54/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.75  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['67', '68'])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.75  thf('71', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X17 @ X18)
% 0.54/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('72', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.54/0.75      inference('sup-', [status(thm)], ['70', '71'])).
% 0.54/0.75  thf(t209_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.54/0.75       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i]:
% 0.54/0.75         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.54/0.75          | ~ (v4_relat_1 @ X10 @ X11)
% 0.54/0.75          | ~ (v1_relat_1 @ X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['72', '73'])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc1_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( v1_relat_1 @ C ) ))).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.75         ((v1_relat_1 @ X14)
% 0.54/0.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.75  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 0.54/0.75      inference('sup-', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('78', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['74', '77'])).
% 0.54/0.75  thf(t2_boole, axiom,
% 0.54/0.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.75  thf('80', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.75  thf('81', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['79', '80'])).
% 0.54/0.75  thf('82', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.75      inference('simplify', [status(thm)], ['81'])).
% 0.54/0.75  thf(t207_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ C ) =>
% 0.54/0.75       ( ( r1_xboole_0 @ A @ B ) =>
% 0.54/0.75         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.75  thf('83', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.75         (~ (r1_xboole_0 @ X7 @ X8)
% 0.54/0.75          | ~ (v1_relat_1 @ X9)
% 0.54/0.75          | ((k7_relat_1 @ (k7_relat_1 @ X9 @ X7) @ X8) = (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.54/0.75  thf('84', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['82', '83'])).
% 0.54/0.75  thf('85', plain,
% 0.54/0.75      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_E))),
% 0.54/0.75      inference('sup+', [status(thm)], ['78', '84'])).
% 0.54/0.75  thf('86', plain, ((v1_relat_1 @ sk_E)),
% 0.54/0.75      inference('sup-', [status(thm)], ['75', '76'])).
% 0.54/0.75  thf('87', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '86'])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('89', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('90', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('91', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.54/0.75          | ~ (v1_funct_1 @ X20)
% 0.54/0.75          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.54/0.75  thf('92', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.54/0.75          | ~ (v1_funct_1 @ sk_F))),
% 0.54/0.75      inference('sup-', [status(thm)], ['90', '91'])).
% 0.54/0.75  thf('93', plain, ((v1_funct_1 @ sk_F)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.75  thf('95', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('96', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X17 @ X18)
% 0.54/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('97', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.54/0.75      inference('sup-', [status(thm)], ['95', '96'])).
% 0.54/0.75  thf('98', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i]:
% 0.54/0.75         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.54/0.75          | ~ (v4_relat_1 @ X10 @ X11)
% 0.54/0.75          | ~ (v1_relat_1 @ X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.54/0.75  thf('99', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('100', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('101', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.75         ((v1_relat_1 @ X14)
% 0.54/0.75          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.75  thf('102', plain, ((v1_relat_1 @ sk_F)),
% 0.54/0.75      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.75  thf('103', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['99', '102'])).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_relat_1 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['82', '83'])).
% 0.54/0.75  thf('105', plain,
% 0.54/0.75      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_F))),
% 0.54/0.75      inference('sup+', [status(thm)], ['103', '104'])).
% 0.54/0.75  thf('106', plain, ((v1_relat_1 @ sk_F)),
% 0.54/0.75      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.75  thf('107', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['105', '106'])).
% 0.54/0.75  thf('108', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('109', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('110', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('111', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('112', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75            = (sk_E))
% 0.54/0.75        | ~ (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['48', '49', '50', '51', '52', '55', '64', '69', '87', '88', 
% 0.54/0.75                 '89', '94', '107', '108', '109', '110', '111'])).
% 0.54/0.75  thf('113', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ~ (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75            = (sk_E))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify', [status(thm)], ['112'])).
% 0.54/0.75  thf('114', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75            = (sk_E))
% 0.54/0.75        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['30', '113'])).
% 0.54/0.75  thf('115', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75            = (sk_E))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify', [status(thm)], ['114'])).
% 0.54/0.75  thf('116', plain,
% 0.54/0.75      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75            != (sk_E))
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            != (sk_F)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('117', plain,
% 0.54/0.75      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75          != (sk_E)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75                = (sk_E))))),
% 0.54/0.75      inference('split', [status(esa)], ['116'])).
% 0.54/0.75  thf('118', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.75  thf('119', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('120', plain,
% 0.54/0.75      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.54/0.75      inference('split', [status(esa)], ['116'])).
% 0.54/0.75  thf('121', plain,
% 0.54/0.75      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['119', '120'])).
% 0.54/0.75  thf('122', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('123', plain,
% 0.54/0.75      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.54/0.75          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.54/0.75      inference('demod', [status(thm)], ['121', '122'])).
% 0.54/0.75  thf('124', plain,
% 0.54/0.75      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.54/0.75          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['118', '123'])).
% 0.54/0.75  thf('125', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('126', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['67', '68'])).
% 0.54/0.75  thf('127', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '86'])).
% 0.54/0.75  thf('128', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('129', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['105', '106'])).
% 0.54/0.75  thf('130', plain,
% 0.54/0.75      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['124', '125', '126', '127', '128', '129'])).
% 0.54/0.75  thf('131', plain,
% 0.54/0.75      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['130'])).
% 0.54/0.75  thf('132', plain,
% 0.54/0.75      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('133', plain,
% 0.54/0.75      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.75  thf('134', plain,
% 0.54/0.75      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75         (k1_zfmisc_1 @ 
% 0.54/0.75          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.75  thf('135', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.75         ((v1_xboole_0 @ X24)
% 0.54/0.75          | (v1_xboole_0 @ X25)
% 0.54/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | ~ (v1_funct_1 @ X27)
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.54/0.75          | ((X30) != (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.54/0.75          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ X30 @ X25)
% 0.54/0.75              = (X27))
% 0.54/0.75          | ~ (m1_subset_1 @ X30 @ 
% 0.54/0.75               (k1_zfmisc_1 @ 
% 0.54/0.75                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X30 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X30)
% 0.54/0.75          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.54/0.75              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.54/0.75                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.54/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | (v1_xboole_0 @ X29)
% 0.54/0.75          | (v1_xboole_0 @ X26))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.54/0.75  thf('136', plain,
% 0.54/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.75         ((v1_xboole_0 @ X26)
% 0.54/0.75          | (v1_xboole_0 @ X29)
% 0.54/0.75          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.54/0.75          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.54/0.75              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.54/0.75                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.54/0.75          | ~ (v1_funct_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.54/0.75          | ~ (v1_funct_2 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.54/0.75               (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.54/0.75          | ~ (m1_subset_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.54/0.75               (k1_zfmisc_1 @ 
% 0.54/0.75                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.54/0.75          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ 
% 0.54/0.75              (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ X25) = (
% 0.54/0.75              X27))
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.54/0.75          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.54/0.75          | ~ (v1_funct_1 @ X27)
% 0.54/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.54/0.75          | (v1_xboole_0 @ X25)
% 0.54/0.75          | (v1_xboole_0 @ X24))),
% 0.54/0.75      inference('simplify', [status(thm)], ['135'])).
% 0.54/0.75  thf('137', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_F)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            = (sk_F))
% 0.54/0.75        | ~ (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.54/0.75            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.54/0.75        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.54/0.75        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.54/0.75        | ~ (v1_funct_1 @ sk_E)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['134', '136'])).
% 0.54/0.75  thf('138', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('139', plain, ((v1_funct_1 @ sk_F)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('140', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('141', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('142', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('143', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('144', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['67', '68'])).
% 0.54/0.75  thf('145', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '86'])).
% 0.54/0.75  thf('146', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('147', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('148', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.54/0.75  thf('149', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['105', '106'])).
% 0.54/0.75  thf('150', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('151', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('152', plain, ((v1_funct_1 @ sk_E)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('153', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('154', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            = (sk_F))
% 0.54/0.75        | ~ (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['137', '138', '139', '140', '141', '142', '143', '144', 
% 0.54/0.75                 '145', '146', '147', '148', '149', '150', '151', '152', '153'])).
% 0.54/0.75  thf('155', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ~ (v1_funct_2 @ 
% 0.54/0.75             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.54/0.75             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            = (sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify', [status(thm)], ['154'])).
% 0.54/0.75  thf('156', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            = (sk_F))
% 0.54/0.75        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['133', '155'])).
% 0.54/0.75  thf('157', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            = (sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify', [status(thm)], ['156'])).
% 0.54/0.75  thf('158', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75            = (sk_F)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['132', '157'])).
% 0.54/0.75  thf('159', plain,
% 0.54/0.75      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75          = (sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify', [status(thm)], ['158'])).
% 0.54/0.75  thf('160', plain,
% 0.54/0.75      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75          != (sk_F)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75                = (sk_F))))),
% 0.54/0.75      inference('split', [status(esa)], ['116'])).
% 0.54/0.75  thf('161', plain,
% 0.54/0.75      (((((sk_F) != (sk_F))
% 0.54/0.75         | (v1_xboole_0 @ sk_D)
% 0.54/0.75         | (v1_xboole_0 @ sk_C)
% 0.54/0.75         | (v1_xboole_0 @ sk_B)
% 0.54/0.75         | (v1_xboole_0 @ sk_A)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75                = (sk_F))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['159', '160'])).
% 0.54/0.75  thf('162', plain,
% 0.54/0.75      ((((v1_xboole_0 @ sk_A)
% 0.54/0.75         | (v1_xboole_0 @ sk_B)
% 0.54/0.75         | (v1_xboole_0 @ sk_C)
% 0.54/0.75         | (v1_xboole_0 @ sk_D)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75                = (sk_F))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['161'])).
% 0.54/0.75  thf('163', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('164', plain,
% 0.54/0.75      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75                = (sk_F))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['162', '163'])).
% 0.54/0.75  thf('165', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('166', plain,
% 0.54/0.75      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75                = (sk_F))))),
% 0.54/0.75      inference('clc', [status(thm)], ['164', '165'])).
% 0.54/0.75  thf('167', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('168', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_B))
% 0.54/0.75         <= (~
% 0.54/0.75             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75                = (sk_F))))),
% 0.54/0.75      inference('clc', [status(thm)], ['166', '167'])).
% 0.54/0.75  thf('169', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('170', plain,
% 0.54/0.75      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75          = (sk_F)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['168', '169'])).
% 0.54/0.75  thf('171', plain,
% 0.54/0.75      (~
% 0.54/0.75       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75          = (sk_E))) | 
% 0.54/0.75       ~
% 0.54/0.75       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.54/0.75          = (sk_F))) | 
% 0.54/0.75       ~
% 0.54/0.75       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.54/0.75          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.54/0.75             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.54/0.75      inference('split', [status(esa)], ['116'])).
% 0.54/0.75  thf('172', plain,
% 0.54/0.75      (~
% 0.54/0.75       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75          = (sk_E)))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['131', '170', '171'])).
% 0.54/0.75  thf('173', plain,
% 0.54/0.75      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.54/0.75         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.54/0.75         != (sk_E))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['117', '172'])).
% 0.54/0.75  thf('174', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['115', '173'])).
% 0.54/0.75  thf('175', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_D)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['15', '174'])).
% 0.54/0.75  thf('176', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_A)
% 0.54/0.75        | (v1_xboole_0 @ sk_B)
% 0.54/0.75        | (v1_xboole_0 @ sk_C)
% 0.54/0.75        | (v1_xboole_0 @ sk_D))),
% 0.54/0.75      inference('simplify', [status(thm)], ['175'])).
% 0.54/0.75  thf('177', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('178', plain,
% 0.54/0.75      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['176', '177'])).
% 0.54/0.75  thf('179', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('180', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.54/0.75      inference('clc', [status(thm)], ['178', '179'])).
% 0.54/0.75  thf('181', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('182', plain, ((v1_xboole_0 @ sk_B)),
% 0.54/0.75      inference('clc', [status(thm)], ['180', '181'])).
% 0.54/0.75  thf('183', plain, ($false), inference('demod', [status(thm)], ['0', '182'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
