%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IGUcdW7FOW

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:03 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 714 expanded)
%              Number of leaves         :   36 ( 222 expanded)
%              Depth                    :   30
%              Number of atoms          : 3429 (29951 expanded)
%              Number of equality atoms :  112 ( 967 expanded)
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X7 ) @ X8 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('84',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('86',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('87',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('94',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('99',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('102',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['97','98'])).

thf('104',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
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
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','84','85','86','91','104','105','106','107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
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
    inference('sup-',[status(thm)],['30','110'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('117',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['113'])).

thf('118',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('120',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('124',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('125',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('126',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103'])).

thf('127',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126'])).

thf('128',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('130',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('132',plain,(
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

thf('133',plain,(
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
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
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
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('142',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('144',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('146',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103'])).

thf('147',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
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
    inference(demod,[status(thm)],['134','135','136','137','138','139','140','141','142','143','144','145','146','147','148','149','150'])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
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
    inference('sup-',[status(thm)],['130','152'])).

thf('154',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
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
    inference('sup-',[status(thm)],['129','154'])).

thf('156',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['113'])).

thf('158',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['113'])).

thf('169',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['128','167','168'])).

thf('170',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['114','169'])).

thf('171',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['112','170'])).

thf('172',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['0','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IGUcdW7FOW
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 172 iterations in 0.145s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.42/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(t6_tmap_1, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61               ( ![D:$i]:
% 0.42/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                   ( ( r1_subset_1 @ C @ D ) =>
% 0.42/0.61                     ( ![E:$i]:
% 0.42/0.61                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61                           ( m1_subset_1 @
% 0.42/0.61                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.61                         ( ![F:$i]:
% 0.42/0.61                           ( ( ( v1_funct_1 @ F ) & 
% 0.42/0.61                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61                               ( m1_subset_1 @
% 0.42/0.61                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61                             ( ( ( k2_partfun1 @
% 0.42/0.61                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.61                                 ( k2_partfun1 @
% 0.42/0.61                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.42/0.61                               ( ( k2_partfun1 @
% 0.42/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.42/0.61                                 ( E ) ) & 
% 0.42/0.61                               ( ( k2_partfun1 @
% 0.42/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.42/0.61                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61              ( ![C:$i]:
% 0.42/0.61                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                  ( ![D:$i]:
% 0.42/0.61                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                      ( ( r1_subset_1 @ C @ D ) =>
% 0.42/0.61                        ( ![E:$i]:
% 0.42/0.61                          ( ( ( v1_funct_1 @ E ) & 
% 0.42/0.61                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61                              ( m1_subset_1 @
% 0.42/0.61                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.61                            ( ![F:$i]:
% 0.42/0.61                              ( ( ( v1_funct_1 @ F ) & 
% 0.42/0.61                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61                                  ( m1_subset_1 @
% 0.42/0.61                                    F @ 
% 0.42/0.61                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61                                ( ( ( k2_partfun1 @
% 0.42/0.61                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.61                                    ( k2_partfun1 @
% 0.42/0.61                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.42/0.61                                  ( ( k2_partfun1 @
% 0.42/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.42/0.61                                    ( E ) ) & 
% 0.42/0.61                                  ( ( k2_partfun1 @
% 0.42/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.42/0.61                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.42/0.61  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k1_tmap_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.42/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.42/0.61         ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.42/0.61         ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.42/0.61         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.42/0.61         ( v1_funct_2 @
% 0.42/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.61           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.42/0.61          | (v1_xboole_0 @ X34)
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.42/0.61          | (v1_xboole_0 @ X32)
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | (v1_xboole_0 @ X35)
% 0.42/0.61          | ~ (v1_funct_1 @ X36)
% 0.42/0.61          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.42/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.42/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | (v1_xboole_0 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.61  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | (v1_xboole_0 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.42/0.61      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '8'])).
% 0.42/0.61  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '12'])).
% 0.42/0.61  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.42/0.61          | (v1_xboole_0 @ X34)
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.42/0.61          | (v1_xboole_0 @ X32)
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | (v1_xboole_0 @ X35)
% 0.42/0.61          | ~ (v1_funct_1 @ X36)
% 0.42/0.61          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.42/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.42/0.61          | (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36) @ 
% 0.42/0.61             (k4_subset_1 @ X35 @ X32 @ X34) @ X33))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.42/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61          | (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['17', '23'])).
% 0.42/0.61  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '27'])).
% 0.42/0.61  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.42/0.61          | (v1_xboole_0 @ X34)
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.42/0.61          | (v1_xboole_0 @ X32)
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | (v1_xboole_0 @ X35)
% 0.42/0.61          | ~ (v1_funct_1 @ X36)
% 0.42/0.61          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.42/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.42/0.61          | (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X32 @ X34) @ X33))))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.61  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.42/0.61      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61          | (m1_subset_1 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['32', '38'])).
% 0.42/0.61  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | (m1_subset_1 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['31', '42'])).
% 0.42/0.61  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.61  thf(d1_tmap_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61               ( ![D:$i]:
% 0.42/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                   ( ![E:$i]:
% 0.42/0.61                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61                         ( m1_subset_1 @
% 0.42/0.61                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.61                       ( ![F:$i]:
% 0.42/0.61                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61                             ( m1_subset_1 @
% 0.42/0.61                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61                           ( ( ( k2_partfun1 @
% 0.42/0.61                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.61                               ( k2_partfun1 @
% 0.42/0.61                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.42/0.61                             ( ![G:$i]:
% 0.42/0.61                               ( ( ( v1_funct_1 @ G ) & 
% 0.42/0.61                                   ( v1_funct_2 @
% 0.42/0.61                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.42/0.61                                   ( m1_subset_1 @
% 0.42/0.61                                     G @ 
% 0.42/0.61                                     ( k1_zfmisc_1 @
% 0.42/0.61                                       ( k2_zfmisc_1 @
% 0.42/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.42/0.61                                 ( ( ( G ) =
% 0.42/0.61                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.42/0.61                                   ( ( ( k2_partfun1 @
% 0.42/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.42/0.61                                         C ) =
% 0.42/0.61                                       ( E ) ) & 
% 0.42/0.61                                     ( ( k2_partfun1 @
% 0.42/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.42/0.61                                         D ) =
% 0.42/0.61                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X24)
% 0.42/0.61          | (v1_xboole_0 @ X25)
% 0.42/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | ~ (v1_funct_1 @ X27)
% 0.42/0.61          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.42/0.61          | ((X30) != (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ X30 @ X29)
% 0.42/0.61              = (X28))
% 0.42/0.61          | ~ (m1_subset_1 @ X30 @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X30 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X30)
% 0.42/0.61          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.42/0.61              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.42/0.61                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.42/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | (v1_xboole_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X26)
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | ~ (v1_funct_1 @ X28)
% 0.42/0.61          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.42/0.61          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.42/0.61              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.42/0.61                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.42/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.42/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.42/0.61               (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ 
% 0.42/0.61              (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ X29) = (
% 0.42/0.61              X28))
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X27)
% 0.42/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | (v1_xboole_0 @ X25)
% 0.42/0.61          | (v1_xboole_0 @ X24))),
% 0.42/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.42/0.61        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.42/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['45', '47'])).
% 0.42/0.61  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.42/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_r1_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.42/0.61       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X12 : $i, X13 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X12)
% 0.42/0.61          | (v1_xboole_0 @ X13)
% 0.42/0.61          | (r1_xboole_0 @ X12 @ X13)
% 0.42/0.61          | ~ (r1_subset_1 @ X12 @ X13))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.42/0.61  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.42/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.42/0.61  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.42/0.61      inference('clc', [status(thm)], ['60', '61'])).
% 0.42/0.61  thf(d7_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.42/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.42/0.61  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k2_partfun1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.42/0.61  thf('66', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E))),
% 0.42/0.61      inference('sup-', [status(thm)], ['65', '66'])).
% 0.42/0.61  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('69', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('70', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc2_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.61  thf('71', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.61         ((v4_relat_1 @ X17 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('72', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.42/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.61  thf(t209_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.42/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.42/0.61  thf('73', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i]:
% 0.42/0.61         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.42/0.61          | ~ (v4_relat_1 @ X10 @ X11)
% 0.42/0.61          | ~ (v1_relat_1 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.42/0.61  thf('74', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['72', '73'])).
% 0.42/0.61  thf('75', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( v1_relat_1 @ C ) ))).
% 0.42/0.61  thf('76', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X14)
% 0.42/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.42/0.61  thf('78', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['74', '77'])).
% 0.42/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.42/0.61  thf('79', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.42/0.61  thf(t207_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ C ) =>
% 0.42/0.61       ( ( r1_xboole_0 @ A @ B ) =>
% 0.42/0.61         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.61  thf('80', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.61         (~ (r1_xboole_0 @ X7 @ X8)
% 0.42/0.61          | ~ (v1_relat_1 @ X9)
% 0.42/0.61          | ((k7_relat_1 @ (k7_relat_1 @ X9 @ X7) @ X8) = (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.42/0.61  thf('81', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['79', '80'])).
% 0.42/0.61  thf('82', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_E))),
% 0.42/0.61      inference('sup+', [status(thm)], ['78', '81'])).
% 0.42/0.61  thf('83', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.42/0.61  thf('84', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.61  thf('85', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('86', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('87', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('88', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.42/0.61  thf('89', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F))),
% 0.42/0.61      inference('sup-', [status(thm)], ['87', '88'])).
% 0.42/0.61  thf('90', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('91', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['89', '90'])).
% 0.42/0.61  thf('92', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('93', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.61         ((v4_relat_1 @ X17 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.61  thf('94', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.42/0.61      inference('sup-', [status(thm)], ['92', '93'])).
% 0.42/0.61  thf('95', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i]:
% 0.42/0.61         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.42/0.61          | ~ (v4_relat_1 @ X10 @ X11)
% 0.42/0.61          | ~ (v1_relat_1 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.42/0.61  thf('96', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['94', '95'])).
% 0.42/0.61  thf('97', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('98', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X14)
% 0.42/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('99', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.61  thf('100', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['96', '99'])).
% 0.42/0.61  thf('101', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['79', '80'])).
% 0.42/0.61  thf('102', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_F))),
% 0.42/0.61      inference('sup+', [status(thm)], ['100', '101'])).
% 0.42/0.61  thf('103', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.61  thf('104', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.42/0.61  thf('105', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('106', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('107', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('108', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('109', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['48', '49', '50', '51', '52', '55', '64', '69', '84', '85', 
% 0.42/0.61                 '86', '91', '104', '105', '106', '107', '108'])).
% 0.42/0.61  thf('110', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['109'])).
% 0.42/0.61  thf('111', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['30', '110'])).
% 0.42/0.61  thf('112', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['111'])).
% 0.42/0.61  thf('113', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            != (sk_E))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            != (sk_F)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('114', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          != (sk_E)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61                = (sk_E))))),
% 0.42/0.61      inference('split', [status(esa)], ['113'])).
% 0.42/0.61  thf('115', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['89', '90'])).
% 0.42/0.61  thf('116', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('117', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('split', [status(esa)], ['113'])).
% 0.42/0.61  thf('118', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['116', '117'])).
% 0.42/0.61  thf('119', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('120', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['118', '119'])).
% 0.42/0.61  thf('121', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.42/0.61          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['115', '120'])).
% 0.42/0.61  thf('122', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('123', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('124', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.61  thf('125', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('126', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.42/0.61  thf('127', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['121', '122', '123', '124', '125', '126'])).
% 0.42/0.61  thf('128', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['127'])).
% 0.42/0.61  thf('129', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf('130', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf('131', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.61  thf('132', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X24)
% 0.42/0.61          | (v1_xboole_0 @ X25)
% 0.42/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | ~ (v1_funct_1 @ X27)
% 0.42/0.61          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.42/0.61          | ((X30) != (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ X30 @ X25)
% 0.42/0.61              = (X27))
% 0.42/0.61          | ~ (m1_subset_1 @ X30 @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X30 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X30)
% 0.42/0.61          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.42/0.61              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.42/0.61                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.42/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | (v1_xboole_0 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.42/0.61  thf('133', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X26)
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | ~ (v1_funct_1 @ X28)
% 0.42/0.61          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.42/0.61          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.42/0.61              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.42/0.61                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.42/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.42/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.42/0.61               (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ 
% 0.42/0.61              (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ X25) = (
% 0.42/0.61              X27))
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.42/0.61          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.42/0.61          | ~ (v1_funct_1 @ X27)
% 0.42/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.42/0.61          | (v1_xboole_0 @ X25)
% 0.42/0.61          | (v1_xboole_0 @ X24))),
% 0.42/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.42/0.61  thf('134', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.42/0.61        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.42/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['131', '133'])).
% 0.42/0.61  thf('135', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('136', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('137', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('138', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('139', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('140', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('141', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('142', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.61  thf('143', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('144', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('145', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['89', '90'])).
% 0.42/0.61  thf('146', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.42/0.61  thf('147', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('148', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('149', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('150', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('151', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['134', '135', '136', '137', '138', '139', '140', '141', 
% 0.42/0.61                 '142', '143', '144', '145', '146', '147', '148', '149', '150'])).
% 0.42/0.61  thf('152', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['151'])).
% 0.42/0.61  thf('153', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['130', '152'])).
% 0.42/0.61  thf('154', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['153'])).
% 0.42/0.61  thf('155', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['129', '154'])).
% 0.42/0.61  thf('156', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['155'])).
% 0.42/0.61  thf('157', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          != (sk_F)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('split', [status(esa)], ['113'])).
% 0.42/0.61  thf('158', plain,
% 0.42/0.61      (((((sk_F) != (sk_F))
% 0.42/0.61         | (v1_xboole_0 @ sk_D)
% 0.42/0.61         | (v1_xboole_0 @ sk_C)
% 0.42/0.61         | (v1_xboole_0 @ sk_B)
% 0.42/0.61         | (v1_xboole_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['156', '157'])).
% 0.42/0.61  thf('159', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_A)
% 0.42/0.61         | (v1_xboole_0 @ sk_B)
% 0.42/0.61         | (v1_xboole_0 @ sk_C)
% 0.42/0.61         | (v1_xboole_0 @ sk_D)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['158'])).
% 0.42/0.61  thf('160', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('161', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['159', '160'])).
% 0.42/0.61  thf('162', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('163', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('clc', [status(thm)], ['161', '162'])).
% 0.42/0.61  thf('164', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('165', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_B))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('clc', [status(thm)], ['163', '164'])).
% 0.42/0.61  thf('166', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('167', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          = (sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['165', '166'])).
% 0.42/0.61  thf('168', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          = (sk_E))) | 
% 0.42/0.61       ~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          = (sk_F))) | 
% 0.42/0.61       ~
% 0.42/0.61       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.42/0.61      inference('split', [status(esa)], ['113'])).
% 0.42/0.61  thf('169', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          = (sk_E)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['128', '167', '168'])).
% 0.42/0.61  thf('170', plain,
% 0.42/0.61      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61         != (sk_E))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['114', '169'])).
% 0.42/0.61  thf('171', plain,
% 0.42/0.61      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['112', '170'])).
% 0.42/0.61  thf('172', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '171'])).
% 0.42/0.61  thf('173', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['172'])).
% 0.42/0.61  thf('174', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('175', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['173', '174'])).
% 0.42/0.61  thf('176', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('177', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.42/0.61      inference('clc', [status(thm)], ['175', '176'])).
% 0.42/0.61  thf('178', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('179', plain, ((v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('clc', [status(thm)], ['177', '178'])).
% 0.42/0.61  thf('180', plain, ($false), inference('demod', [status(thm)], ['0', '179'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
