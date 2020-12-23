%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Vw0eSu5On

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:05 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 600 expanded)
%              Number of leaves         :   31 ( 184 expanded)
%              Depth                    :   40
%              Number of atoms          : 3657 (27374 expanded)
%              Number of equality atoms :  132 ( 885 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('7',plain,(
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
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28 ) @ ( k4_subset_1 @ X27 @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X27 @ X24 @ X26 ) @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
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
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ( X22
       != ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 @ X22 @ X21 )
        = X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k2_partfun1 @ X21 @ X16 @ X20 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) )
       != ( k2_partfun1 @ X17 @ X16 @ X19 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X16 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X16 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X16 ) ) )
      | ( ( k2_partfun1 @ X21 @ X16 @ X20 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) )
       != ( k2_partfun1 @ X17 @ X16 @ X19 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) @ X21 )
        = X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
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
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X5 @ X3 @ X4 )
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['62','63'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k2_partfun1 @ X13 @ X14 @ X12 @ X15 )
        = ( k7_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('74',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k2_partfun1 @ X13 @ X14 @ X12 @ X15 )
        = ( k7_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
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
    inference(demod,[status(thm)],['50','51','52','53','54','57','66','71','72','73','78','79','80','81','82'])).

thf('84',plain,
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
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
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
    inference('sup-',[status(thm)],['32','84'])).

thf('86',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('90',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('93',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['87'])).

thf('94',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('96',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('98',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('101',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['90','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('104',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('105',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['89','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('110',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('114',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('118',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ( X22
       != ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 @ X22 @ X17 )
        = X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k2_partfun1 @ X21 @ X16 @ X20 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) )
       != ( k2_partfun1 @ X17 @ X16 @ X19 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X16 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('119',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X16 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X16 ) ) )
      | ( ( k2_partfun1 @ X21 @ X16 @ X20 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) )
       != ( k2_partfun1 @ X17 @ X16 @ X19 @ ( k9_subset_1 @ X18 @ X21 @ X17 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X18 @ X21 @ X17 ) @ X16 @ ( k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19 ) @ X17 )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
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
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('126',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('131',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
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
    inference(demod,[status(thm)],['120','121','122','123','124','125','126','127','128','129','130','131','132','133','134'])).

thf('136',plain,
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
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
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
    inference('sup-',[status(thm)],['116','136'])).

thf('138',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','138'])).

thf('140',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['114','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['103','104'])).

thf('143',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['113','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['108','109'])).

thf('146',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['87'])).

thf('149',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['87'])).

thf('160',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['112','158','159'])).

thf('161',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['88','160'])).

thf('162',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['86','161'])).

thf('163',plain,
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
    inference('sup-',[status(thm)],['17','162'])).

thf('164',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['103','104'])).

thf('167',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['108','109'])).

thf('170',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    $false ),
    inference(demod,[status(thm)],['0','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Vw0eSu5On
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 134 iterations in 0.169s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.40/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.40/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.63  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.63  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.40/0.63  thf(t6_tmap_1, conjecture,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.63           ( ![C:$i]:
% 0.40/0.63             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63               ( ![D:$i]:
% 0.40/0.63                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.40/0.63                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63                   ( ( r1_subset_1 @ C @ D ) =>
% 0.40/0.63                     ( ![E:$i]:
% 0.40/0.63                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.40/0.63                           ( m1_subset_1 @
% 0.40/0.63                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.40/0.63                         ( ![F:$i]:
% 0.40/0.63                           ( ( ( v1_funct_1 @ F ) & 
% 0.40/0.63                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.40/0.63                               ( m1_subset_1 @
% 0.40/0.63                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.40/0.63                             ( ( ( k2_partfun1 @
% 0.40/0.63                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.40/0.63                                 ( k2_partfun1 @
% 0.40/0.63                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.40/0.63                               ( ( k2_partfun1 @
% 0.40/0.63                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.40/0.63                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.40/0.63                                 ( E ) ) & 
% 0.40/0.63                               ( ( k2_partfun1 @
% 0.40/0.63                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.40/0.63                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.40/0.63                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i]:
% 0.40/0.63        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.63          ( ![B:$i]:
% 0.40/0.63            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.63              ( ![C:$i]:
% 0.40/0.63                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63                  ( ![D:$i]:
% 0.40/0.63                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.40/0.63                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63                      ( ( r1_subset_1 @ C @ D ) =>
% 0.40/0.63                        ( ![E:$i]:
% 0.40/0.63                          ( ( ( v1_funct_1 @ E ) & 
% 0.40/0.63                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.40/0.63                              ( m1_subset_1 @
% 0.40/0.63                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.40/0.63                            ( ![F:$i]:
% 0.40/0.63                              ( ( ( v1_funct_1 @ F ) & 
% 0.40/0.63                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.40/0.63                                  ( m1_subset_1 @
% 0.40/0.63                                    F @ 
% 0.40/0.63                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.40/0.63                                ( ( ( k2_partfun1 @
% 0.40/0.63                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.40/0.63                                    ( k2_partfun1 @
% 0.40/0.63                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.40/0.63                                  ( ( k2_partfun1 @
% 0.40/0.63                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.40/0.63                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.40/0.63                                    ( E ) ) & 
% 0.40/0.63                                  ( ( k2_partfun1 @
% 0.40/0.63                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.40/0.63                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.40/0.63                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.40/0.63  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t110_relat_1, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( v1_relat_1 @ A ) =>
% 0.40/0.63       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      (![X6 : $i]:
% 0.40/0.63         (((k7_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.63          | ~ (v1_relat_1 @ X6))),
% 0.40/0.63      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      (![X6 : $i]:
% 0.40/0.63         (((k7_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.63          | ~ (v1_relat_1 @ X6))),
% 0.40/0.63      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.40/0.63  thf('3', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('4', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('5', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(dt_k1_tmap_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.63     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ D ) ) & 
% 0.40/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.40/0.63         ( v1_funct_2 @ E @ C @ B ) & 
% 0.40/0.63         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.40/0.63         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.40/0.63         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.40/0.63       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.40/0.63         ( v1_funct_2 @
% 0.40/0.63           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.40/0.63           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.40/0.63         ( m1_subset_1 @
% 0.40/0.63           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.40/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.40/0.63  thf('6', plain,
% 0.40/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.63          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.40/0.63          | ~ (v1_funct_1 @ X23)
% 0.40/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.40/0.63          | (v1_xboole_0 @ X26)
% 0.40/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X27))
% 0.40/0.63          | (v1_xboole_0 @ X24)
% 0.40/0.63          | (v1_xboole_0 @ X25)
% 0.40/0.63          | (v1_xboole_0 @ X27)
% 0.40/0.63          | ~ (v1_funct_1 @ X28)
% 0.40/0.63          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.40/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.40/0.63          | (v1_funct_1 @ (k1_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28)))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.40/0.63  thf('7', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.40/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.40/0.63          | ~ (v1_funct_1 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ X2)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.40/0.63          | (v1_xboole_0 @ X1)
% 0.40/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.40/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.40/0.63          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.63  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('10', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.40/0.63          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.40/0.63          | ~ (v1_funct_1 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ X2)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.40/0.63          | (v1_xboole_0 @ X1)
% 0.40/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.40/0.63      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_D)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (v1_funct_1 @ sk_F)
% 0.40/0.63          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.40/0.63          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['4', '10'])).
% 0.40/0.63  thf('12', plain, ((v1_funct_1 @ sk_F)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('13', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_D)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.40/0.63      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.40/0.63  thf('15', plain,
% 0.40/0.63      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['3', '14'])).
% 0.40/0.63  thf('16', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.63  thf('18', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('19', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.63          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.40/0.63          | ~ (v1_funct_1 @ X23)
% 0.40/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.40/0.63          | (v1_xboole_0 @ X26)
% 0.40/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X27))
% 0.40/0.63          | (v1_xboole_0 @ X24)
% 0.40/0.63          | (v1_xboole_0 @ X25)
% 0.40/0.63          | (v1_xboole_0 @ X27)
% 0.40/0.63          | ~ (v1_funct_1 @ X28)
% 0.40/0.63          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.40/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.40/0.63          | (v1_funct_2 @ (k1_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28) @ 
% 0.40/0.63             (k4_subset_1 @ X27 @ X24 @ X26) @ X25))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.40/0.63           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.40/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.40/0.63          | ~ (v1_funct_1 @ X2)
% 0.40/0.63          | (v1_xboole_0 @ X1)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.40/0.63          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.63  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('24', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.40/0.63           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.40/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.40/0.63          | ~ (v1_funct_1 @ X2)
% 0.40/0.63          | (v1_xboole_0 @ X1)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.40/0.63      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.40/0.63  thf('26', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_D)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (v1_funct_1 @ sk_F)
% 0.40/0.63          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.40/0.63          | (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['19', '25'])).
% 0.40/0.63  thf('27', plain, ((v1_funct_1 @ sk_F)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('28', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_D)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['18', '29'])).
% 0.40/0.63  thf('31', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('32', plain,
% 0.40/0.63      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.63  thf('33', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('34', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('35', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('36', plain,
% 0.40/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.63          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.40/0.63          | ~ (v1_funct_1 @ X23)
% 0.40/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.40/0.63          | (v1_xboole_0 @ X26)
% 0.40/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X27))
% 0.40/0.63          | (v1_xboole_0 @ X24)
% 0.40/0.63          | (v1_xboole_0 @ X25)
% 0.40/0.63          | (v1_xboole_0 @ X27)
% 0.40/0.63          | ~ (v1_funct_1 @ X28)
% 0.40/0.63          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.40/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.40/0.63          | (m1_subset_1 @ (k1_tmap_1 @ X27 @ X25 @ X24 @ X26 @ X23 @ X28) @ 
% 0.40/0.63             (k1_zfmisc_1 @ 
% 0.40/0.63              (k2_zfmisc_1 @ (k4_subset_1 @ X27 @ X24 @ X26) @ X25))))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.40/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.40/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.40/0.63          | ~ (v1_funct_1 @ X2)
% 0.40/0.63          | (v1_xboole_0 @ X1)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | ~ (v1_funct_1 @ sk_E)
% 0.40/0.63          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.63  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('39', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.40/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.40/0.63          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.40/0.63          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.40/0.63          | ~ (v1_funct_1 @ X2)
% 0.40/0.63          | (v1_xboole_0 @ X1)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.40/0.63      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_D)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | ~ (v1_funct_1 @ sk_F)
% 0.40/0.63          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.40/0.63          | (m1_subset_1 @ 
% 0.40/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k1_zfmisc_1 @ 
% 0.40/0.63              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['34', '40'])).
% 0.40/0.63  thf('42', plain, ((v1_funct_1 @ sk_F)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('43', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('44', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_D)
% 0.40/0.63          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.40/0.63          | (v1_xboole_0 @ sk_C)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v1_xboole_0 @ X0)
% 0.40/0.63          | (m1_subset_1 @ 
% 0.40/0.63             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k1_zfmisc_1 @ 
% 0.40/0.63              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.40/0.63      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63         (k1_zfmisc_1 @ 
% 0.40/0.63          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['33', '44'])).
% 0.40/0.63  thf('46', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('47', plain,
% 0.40/0.63      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63         (k1_zfmisc_1 @ 
% 0.40/0.63          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.63  thf(d1_tmap_1, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.63           ( ![C:$i]:
% 0.40/0.63             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63               ( ![D:$i]:
% 0.40/0.63                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.40/0.63                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.63                   ( ![E:$i]:
% 0.40/0.63                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.40/0.63                         ( m1_subset_1 @
% 0.40/0.63                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.40/0.63                       ( ![F:$i]:
% 0.40/0.63                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.40/0.63                             ( m1_subset_1 @
% 0.40/0.63                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.40/0.63                           ( ( ( k2_partfun1 @
% 0.40/0.63                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.40/0.63                               ( k2_partfun1 @
% 0.40/0.63                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.40/0.63                             ( ![G:$i]:
% 0.40/0.63                               ( ( ( v1_funct_1 @ G ) & 
% 0.40/0.63                                   ( v1_funct_2 @
% 0.40/0.63                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.40/0.63                                   ( m1_subset_1 @
% 0.40/0.63                                     G @ 
% 0.40/0.63                                     ( k1_zfmisc_1 @
% 0.40/0.63                                       ( k2_zfmisc_1 @
% 0.40/0.63                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.40/0.63                                 ( ( ( G ) =
% 0.40/0.63                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.40/0.63                                   ( ( ( k2_partfun1 @
% 0.40/0.63                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.40/0.63                                         C ) =
% 0.40/0.63                                       ( E ) ) & 
% 0.40/0.63                                     ( ( k2_partfun1 @
% 0.40/0.63                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.40/0.63                                         D ) =
% 0.40/0.63                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.63  thf('48', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X16)
% 0.40/0.63          | (v1_xboole_0 @ X17)
% 0.40/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | ~ (v1_funct_1 @ X19)
% 0.40/0.63          | ~ (v1_funct_2 @ X19 @ X17 @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.40/0.63          | ((X22) != (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19))
% 0.40/0.63          | ((k2_partfun1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16 @ X22 @ X21)
% 0.40/0.63              = (X20))
% 0.40/0.63          | ~ (m1_subset_1 @ X22 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (k2_zfmisc_1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16)))
% 0.40/0.63          | ~ (v1_funct_2 @ X22 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16)
% 0.40/0.63          | ~ (v1_funct_1 @ X22)
% 0.40/0.63          | ((k2_partfun1 @ X21 @ X16 @ X20 @ (k9_subset_1 @ X18 @ X21 @ X17))
% 0.40/0.63              != (k2_partfun1 @ X17 @ X16 @ X19 @ 
% 0.40/0.63                  (k9_subset_1 @ X18 @ X21 @ X17)))
% 0.40/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X16)))
% 0.40/0.63          | ~ (v1_funct_2 @ X20 @ X21 @ X16)
% 0.40/0.63          | ~ (v1_funct_1 @ X20)
% 0.40/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | (v1_xboole_0 @ X21)
% 0.40/0.63          | (v1_xboole_0 @ X18))),
% 0.40/0.63      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.40/0.63  thf('49', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X18)
% 0.40/0.63          | (v1_xboole_0 @ X21)
% 0.40/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | ~ (v1_funct_1 @ X20)
% 0.40/0.63          | ~ (v1_funct_2 @ X20 @ X21 @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X16)))
% 0.40/0.63          | ((k2_partfun1 @ X21 @ X16 @ X20 @ (k9_subset_1 @ X18 @ X21 @ X17))
% 0.40/0.63              != (k2_partfun1 @ X17 @ X16 @ X19 @ 
% 0.40/0.63                  (k9_subset_1 @ X18 @ X21 @ X17)))
% 0.40/0.63          | ~ (v1_funct_1 @ (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19))
% 0.40/0.63          | ~ (v1_funct_2 @ (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19) @ 
% 0.40/0.63               (k4_subset_1 @ X18 @ X21 @ X17) @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19) @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (k2_zfmisc_1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16)))
% 0.40/0.63          | ((k2_partfun1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16 @ 
% 0.40/0.63              (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19) @ X21) = (
% 0.40/0.63              X20))
% 0.40/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.40/0.63          | ~ (v1_funct_2 @ X19 @ X17 @ X16)
% 0.40/0.63          | ~ (v1_funct_1 @ X19)
% 0.40/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | (v1_xboole_0 @ X17)
% 0.40/0.63          | (v1_xboole_0 @ X16))),
% 0.40/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.63  thf('50', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | ~ (v1_funct_1 @ sk_F)
% 0.40/0.63        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63            = (sk_E))
% 0.40/0.63        | ~ (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.40/0.63        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.40/0.63        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ sk_E)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['47', '49'])).
% 0.40/0.63  thf('51', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('52', plain, ((v1_funct_1 @ sk_F)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('53', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('54', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('55', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k9_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.63       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.63  thf('56', plain,
% 0.40/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.63         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 0.40/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.40/0.63  thf('57', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('58', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_r1_subset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.40/0.63       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.40/0.63  thf('59', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X7)
% 0.40/0.63          | (v1_xboole_0 @ X8)
% 0.40/0.63          | (r1_xboole_0 @ X7 @ X8)
% 0.40/0.63          | ~ (r1_subset_1 @ X7 @ X8))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.40/0.63  thf('60', plain,
% 0.40/0.63      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.63  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('62', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.40/0.63      inference('clc', [status(thm)], ['60', '61'])).
% 0.40/0.63  thf('63', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('64', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.40/0.63      inference('clc', [status(thm)], ['62', '63'])).
% 0.40/0.63  thf(d7_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.63       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.63  thf('65', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.63      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.63  thf('66', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('67', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(redefinition_k2_partfun1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.63     ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.63       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.40/0.63  thf('68', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.63          | ~ (v1_funct_1 @ X12)
% 0.40/0.63          | ((k2_partfun1 @ X13 @ X14 @ X12 @ X15) = (k7_relat_1 @ X12 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.40/0.63  thf('69', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.40/0.63          | ~ (v1_funct_1 @ sk_E))),
% 0.40/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.40/0.63  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('71', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.63  thf('72', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('73', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('74', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('75', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.40/0.63          | ~ (v1_funct_1 @ X12)
% 0.40/0.63          | ((k2_partfun1 @ X13 @ X14 @ X12 @ X15) = (k7_relat_1 @ X12 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.40/0.63  thf('76', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.40/0.63          | ~ (v1_funct_1 @ sk_F))),
% 0.40/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.40/0.63  thf('77', plain, ((v1_funct_1 @ sk_F)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('78', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.63  thf('79', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('80', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('81', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('82', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('83', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63            = (sk_E))
% 0.40/0.63        | ~ (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.40/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)],
% 0.40/0.63                ['50', '51', '52', '53', '54', '57', '66', '71', '72', '73', 
% 0.40/0.63                 '78', '79', '80', '81', '82'])).
% 0.40/0.63  thf('84', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ~ (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63            = (sk_E))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify', [status(thm)], ['83'])).
% 0.40/0.63  thf('85', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63            = (sk_E))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.40/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['32', '84'])).
% 0.40/0.63  thf('86', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63            = (sk_E))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify', [status(thm)], ['85'])).
% 0.40/0.63  thf('87', plain,
% 0.40/0.63      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63            != (sk_E))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            != (sk_F)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('88', plain,
% 0.40/0.63      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63          != (sk_E)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63                = (sk_E))))),
% 0.40/0.63      inference('split', [status(esa)], ['87'])).
% 0.40/0.63  thf('89', plain,
% 0.40/0.63      (![X6 : $i]:
% 0.40/0.63         (((k7_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.63          | ~ (v1_relat_1 @ X6))),
% 0.40/0.63      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.40/0.63  thf('90', plain,
% 0.40/0.63      (![X6 : $i]:
% 0.40/0.63         (((k7_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.63          | ~ (v1_relat_1 @ X6))),
% 0.40/0.63      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.40/0.63  thf('91', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.63  thf('92', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('93', plain,
% 0.40/0.63      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('split', [status(esa)], ['87'])).
% 0.40/0.63  thf('94', plain,
% 0.40/0.63      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.40/0.63  thf('95', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('96', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('97', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('98', plain,
% 0.40/0.63      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.40/0.63          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.40/0.63  thf('99', plain,
% 0.40/0.63      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.40/0.63          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['91', '98'])).
% 0.40/0.63  thf('100', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.63  thf('101', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['99', '100'])).
% 0.40/0.63  thf('102', plain,
% 0.40/0.63      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63         | ~ (v1_relat_1 @ sk_F)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['90', '101'])).
% 0.40/0.63  thf('103', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(cc1_relset_1, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.63       ( v1_relat_1 @ C ) ))).
% 0.40/0.63  thf('104', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.63         ((v1_relat_1 @ X9)
% 0.40/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.63  thf('105', plain, ((v1_relat_1 @ sk_F)),
% 0.40/0.63      inference('sup-', [status(thm)], ['103', '104'])).
% 0.40/0.63  thf('106', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['102', '105'])).
% 0.40/0.63  thf('107', plain,
% 0.40/0.63      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['89', '106'])).
% 0.40/0.63  thf('108', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('109', plain,
% 0.40/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.63         ((v1_relat_1 @ X9)
% 0.40/0.63          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.40/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.63  thf('110', plain, ((v1_relat_1 @ sk_E)),
% 0.40/0.63      inference('sup-', [status(thm)], ['108', '109'])).
% 0.40/0.63  thf('111', plain,
% 0.40/0.63      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['107', '110'])).
% 0.40/0.63  thf('112', plain,
% 0.40/0.63      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.40/0.63      inference('simplify', [status(thm)], ['111'])).
% 0.40/0.63  thf('113', plain,
% 0.40/0.63      (![X6 : $i]:
% 0.40/0.63         (((k7_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.63          | ~ (v1_relat_1 @ X6))),
% 0.40/0.63      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.40/0.63  thf('114', plain,
% 0.40/0.63      (![X6 : $i]:
% 0.40/0.63         (((k7_relat_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.63          | ~ (v1_relat_1 @ X6))),
% 0.40/0.63      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.40/0.63  thf('115', plain,
% 0.40/0.63      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.63  thf('116', plain,
% 0.40/0.63      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.63  thf('117', plain,
% 0.40/0.63      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63         (k1_zfmisc_1 @ 
% 0.40/0.63          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.63  thf('118', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X16)
% 0.40/0.63          | (v1_xboole_0 @ X17)
% 0.40/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | ~ (v1_funct_1 @ X19)
% 0.40/0.63          | ~ (v1_funct_2 @ X19 @ X17 @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.40/0.63          | ((X22) != (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19))
% 0.40/0.63          | ((k2_partfun1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16 @ X22 @ X17)
% 0.40/0.63              = (X19))
% 0.40/0.63          | ~ (m1_subset_1 @ X22 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (k2_zfmisc_1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16)))
% 0.40/0.63          | ~ (v1_funct_2 @ X22 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16)
% 0.40/0.63          | ~ (v1_funct_1 @ X22)
% 0.40/0.63          | ((k2_partfun1 @ X21 @ X16 @ X20 @ (k9_subset_1 @ X18 @ X21 @ X17))
% 0.40/0.63              != (k2_partfun1 @ X17 @ X16 @ X19 @ 
% 0.40/0.63                  (k9_subset_1 @ X18 @ X21 @ X17)))
% 0.40/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X16)))
% 0.40/0.63          | ~ (v1_funct_2 @ X20 @ X21 @ X16)
% 0.40/0.63          | ~ (v1_funct_1 @ X20)
% 0.40/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | (v1_xboole_0 @ X21)
% 0.40/0.63          | (v1_xboole_0 @ X18))),
% 0.40/0.63      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.40/0.63  thf('119', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X18)
% 0.40/0.63          | (v1_xboole_0 @ X21)
% 0.40/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | ~ (v1_funct_1 @ X20)
% 0.40/0.63          | ~ (v1_funct_2 @ X20 @ X21 @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X16)))
% 0.40/0.63          | ((k2_partfun1 @ X21 @ X16 @ X20 @ (k9_subset_1 @ X18 @ X21 @ X17))
% 0.40/0.63              != (k2_partfun1 @ X17 @ X16 @ X19 @ 
% 0.40/0.63                  (k9_subset_1 @ X18 @ X21 @ X17)))
% 0.40/0.63          | ~ (v1_funct_1 @ (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19))
% 0.40/0.63          | ~ (v1_funct_2 @ (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19) @ 
% 0.40/0.63               (k4_subset_1 @ X18 @ X21 @ X17) @ X16)
% 0.40/0.63          | ~ (m1_subset_1 @ (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19) @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (k2_zfmisc_1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16)))
% 0.40/0.63          | ((k2_partfun1 @ (k4_subset_1 @ X18 @ X21 @ X17) @ X16 @ 
% 0.40/0.63              (k1_tmap_1 @ X18 @ X16 @ X21 @ X17 @ X20 @ X19) @ X17) = (
% 0.40/0.63              X19))
% 0.40/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.40/0.63          | ~ (v1_funct_2 @ X19 @ X17 @ X16)
% 0.40/0.63          | ~ (v1_funct_1 @ X19)
% 0.40/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.40/0.63          | (v1_xboole_0 @ X17)
% 0.40/0.63          | (v1_xboole_0 @ X16))),
% 0.40/0.63      inference('simplify', [status(thm)], ['118'])).
% 0.40/0.63  thf('120', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | ~ (v1_funct_1 @ sk_F)
% 0.40/0.63        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | ~ (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.40/0.63            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.40/0.63        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.40/0.63        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ sk_E)
% 0.40/0.63        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['117', '119'])).
% 0.40/0.63  thf('121', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('122', plain, ((v1_funct_1 @ sk_F)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('123', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('124', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('125', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('126', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('127', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.63  thf('128', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.63  thf('129', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.63  thf('130', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.63  thf('131', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('132', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('133', plain, ((v1_funct_1 @ sk_E)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('134', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('135', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | ~ (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.40/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)],
% 0.40/0.63                ['120', '121', '122', '123', '124', '125', '126', '127', 
% 0.40/0.63                 '128', '129', '130', '131', '132', '133', '134'])).
% 0.40/0.63  thf('136', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ~ (v1_funct_2 @ 
% 0.40/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.40/0.63             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify', [status(thm)], ['135'])).
% 0.40/0.63  thf('137', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.40/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['116', '136'])).
% 0.40/0.63  thf('138', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify', [status(thm)], ['137'])).
% 0.40/0.63  thf('139', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.40/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['115', '138'])).
% 0.40/0.63  thf('140', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify', [status(thm)], ['139'])).
% 0.40/0.63  thf('141', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | ~ (v1_relat_1 @ sk_F)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['114', '140'])).
% 0.40/0.63  thf('142', plain, ((v1_relat_1 @ sk_F)),
% 0.40/0.63      inference('sup-', [status(thm)], ['103', '104'])).
% 0.40/0.63  thf('143', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F)))),
% 0.40/0.63      inference('demod', [status(thm)], ['141', '142'])).
% 0.40/0.63  thf('144', plain,
% 0.40/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | ~ (v1_relat_1 @ sk_E)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['113', '143'])).
% 0.40/0.63  thf('145', plain, ((v1_relat_1 @ sk_E)),
% 0.40/0.63      inference('sup-', [status(thm)], ['108', '109'])).
% 0.40/0.63  thf('146', plain,
% 0.40/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['144', '145'])).
% 0.40/0.63  thf('147', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63            = (sk_F)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['146'])).
% 0.40/0.63  thf('148', plain,
% 0.40/0.63      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63          != (sk_F)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63                = (sk_F))))),
% 0.40/0.63      inference('split', [status(esa)], ['87'])).
% 0.40/0.63  thf('149', plain,
% 0.40/0.63      (((((sk_F) != (sk_F))
% 0.40/0.63         | (v1_xboole_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v1_xboole_0 @ sk_C)
% 0.40/0.63         | (v1_xboole_0 @ sk_D)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63                = (sk_F))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['147', '148'])).
% 0.40/0.63  thf('150', plain,
% 0.40/0.63      ((((v1_xboole_0 @ sk_D)
% 0.40/0.63         | (v1_xboole_0 @ sk_C)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v1_xboole_0 @ sk_A)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63                = (sk_F))))),
% 0.40/0.63      inference('simplify', [status(thm)], ['149'])).
% 0.40/0.63  thf('151', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('152', plain,
% 0.40/0.63      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63                = (sk_F))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['150', '151'])).
% 0.40/0.63  thf('153', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('154', plain,
% 0.40/0.63      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B)))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63                = (sk_F))))),
% 0.40/0.63      inference('clc', [status(thm)], ['152', '153'])).
% 0.40/0.63  thf('155', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('156', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_B))
% 0.40/0.63         <= (~
% 0.40/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63                = (sk_F))))),
% 0.40/0.63      inference('clc', [status(thm)], ['154', '155'])).
% 0.40/0.63  thf('157', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('158', plain,
% 0.40/0.63      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63          = (sk_F)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['156', '157'])).
% 0.40/0.63  thf('159', plain,
% 0.40/0.63      (~
% 0.40/0.63       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63          = (sk_E))) | 
% 0.40/0.63       ~
% 0.40/0.63       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.40/0.63          = (sk_F))) | 
% 0.40/0.63       ~
% 0.40/0.63       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.40/0.63          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.40/0.63             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.40/0.63      inference('split', [status(esa)], ['87'])).
% 0.40/0.63  thf('160', plain,
% 0.40/0.63      (~
% 0.40/0.63       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63          = (sk_E)))),
% 0.40/0.63      inference('sat_resolution*', [status(thm)], ['112', '158', '159'])).
% 0.40/0.63  thf('161', plain,
% 0.40/0.63      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.40/0.63         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.40/0.63         != (sk_E))),
% 0.40/0.63      inference('simpl_trail', [status(thm)], ['88', '160'])).
% 0.40/0.63  thf('162', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify_reflect-', [status(thm)], ['86', '161'])).
% 0.40/0.63  thf('163', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.40/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['17', '162'])).
% 0.40/0.63  thf('164', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('simplify', [status(thm)], ['163'])).
% 0.40/0.63  thf('165', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | ~ (v1_relat_1 @ sk_F)
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['2', '164'])).
% 0.40/0.63  thf('166', plain, ((v1_relat_1 @ sk_F)),
% 0.40/0.63      inference('sup-', [status(thm)], ['103', '104'])).
% 0.40/0.63  thf('167', plain,
% 0.40/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | (v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['165', '166'])).
% 0.40/0.63  thf('168', plain,
% 0.40/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | ~ (v1_relat_1 @ sk_E)
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('sup-', [status(thm)], ['1', '167'])).
% 0.40/0.63  thf('169', plain, ((v1_relat_1 @ sk_E)),
% 0.40/0.63      inference('sup-', [status(thm)], ['108', '109'])).
% 0.40/0.63  thf('170', plain,
% 0.40/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.63        | (v1_xboole_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_D))),
% 0.40/0.63      inference('demod', [status(thm)], ['168', '169'])).
% 0.40/0.63  thf('171', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_D)
% 0.40/0.63        | (v1_xboole_0 @ sk_C)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v1_xboole_0 @ sk_A))),
% 0.40/0.63      inference('simplify', [status(thm)], ['170'])).
% 0.40/0.63  thf('172', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('173', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.40/0.63      inference('sup-', [status(thm)], ['171', '172'])).
% 0.40/0.63  thf('174', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('175', plain, (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.40/0.63      inference('clc', [status(thm)], ['173', '174'])).
% 0.40/0.63  thf('176', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('177', plain, ((v1_xboole_0 @ sk_B)),
% 0.40/0.63      inference('clc', [status(thm)], ['175', '176'])).
% 0.40/0.63  thf('178', plain, ($false), inference('demod', [status(thm)], ['0', '177'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
