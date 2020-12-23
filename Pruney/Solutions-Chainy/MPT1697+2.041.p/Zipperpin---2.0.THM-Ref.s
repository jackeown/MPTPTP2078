%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DByyTDVYD5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:59 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 691 expanded)
%              Number of leaves         :   35 ( 215 expanded)
%              Depth                    :   40
%              Number of atoms          : 3737 (27956 expanded)
%              Number of equality atoms :  143 ( 963 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X33 @ X31 @ X30 @ X32 @ X29 @ X34 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X33 @ X31 @ X30 @ X32 @ X29 @ X34 ) @ ( k4_subset_1 @ X33 @ X30 @ X32 ) @ X31 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X33 @ X31 @ X30 @ X32 @ X29 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X30 @ X32 ) @ X31 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ( X28
       != ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 @ X28 @ X27 )
        = X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X27 @ X22 @ X26 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) )
       != ( k2_partfun1 @ X23 @ X22 @ X25 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X22 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X22 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X22 ) ) )
      | ( ( k2_partfun1 @ X27 @ X22 @ X26 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) )
       != ( k2_partfun1 @ X23 @ X22 @ X25 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) @ X27 )
        = X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_subset_1 @ X13 @ X14 ) ) ),
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

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('69',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('78',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k2_partfun1 @ X19 @ X20 @ X18 @ X21 )
        = ( k7_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('84',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k2_partfun1 @ X19 @ X20 @ X18 @ X21 )
        = ( k7_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
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
    inference(demod,[status(thm)],['50','51','52','53','54','57','76','81','82','83','88','89','90','91','92'])).

thf('94',plain,
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
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
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
    inference('sup-',[status(thm)],['32','94'])).

thf('96',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('100',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('103',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('104',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('108',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('111',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['100','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('114',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('115',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['99','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('120',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['117','120'])).

thf('122',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('124',plain,(
    ! [X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('125',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('128',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ( X28
       != ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 @ X28 @ X23 )
        = X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X27 @ X22 @ X26 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) )
       != ( k2_partfun1 @ X23 @ X22 @ X25 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X22 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('129',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X22 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X22 ) ) )
      | ( ( k2_partfun1 @ X27 @ X22 @ X26 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) )
       != ( k2_partfun1 @ X23 @ X22 @ X25 @ ( k9_subset_1 @ X24 @ X27 @ X23 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X24 @ X27 @ X23 ) @ X22 @ ( k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25 ) @ X23 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    inference('sup-',[status(thm)],['55','56'])).

thf('136',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('139',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('141',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
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
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137','138','139','140','141','142','143','144'])).

thf('146',plain,
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
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
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
    inference('sup-',[status(thm)],['126','146'])).

thf('148',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['125','148'])).

thf('150',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['124','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['113','114'])).

thf('153',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['123','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['118','119'])).

thf('156',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['97'])).

thf('159',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('170',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['122','168','169'])).

thf('171',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['98','170'])).

thf('172',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['96','171'])).

thf('173',plain,
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
    inference('sup-',[status(thm)],['17','172'])).

thf('174',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['113','114'])).

thf('177',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['118','119'])).

thf('180',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    $false ),
    inference(demod,[status(thm)],['0','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DByyTDVYD5
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.55/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.77  % Solved by: fo/fo7.sh
% 0.55/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.77  % done 219 iterations in 0.308s
% 0.55/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.77  % SZS output start Refutation
% 0.55/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.77  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.55/0.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.55/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.77  thf(sk_E_type, type, sk_E: $i).
% 0.55/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.77  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.55/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.77  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.55/0.77  thf(sk_F_type, type, sk_F: $i).
% 0.55/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.77  thf(t6_tmap_1, conjecture,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.55/0.77           ( ![C:$i]:
% 0.55/0.77             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.55/0.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77               ( ![D:$i]:
% 0.55/0.77                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.55/0.77                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77                   ( ( r1_subset_1 @ C @ D ) =>
% 0.55/0.77                     ( ![E:$i]:
% 0.55/0.77                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.55/0.77                           ( m1_subset_1 @
% 0.55/0.77                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.55/0.77                         ( ![F:$i]:
% 0.55/0.77                           ( ( ( v1_funct_1 @ F ) & 
% 0.55/0.77                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.55/0.77                               ( m1_subset_1 @
% 0.55/0.77                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.55/0.77                             ( ( ( k2_partfun1 @
% 0.55/0.77                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.55/0.77                                 ( k2_partfun1 @
% 0.55/0.77                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.55/0.77                               ( ( k2_partfun1 @
% 0.55/0.77                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.55/0.77                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.55/0.77                                 ( E ) ) & 
% 0.55/0.77                               ( ( k2_partfun1 @
% 0.55/0.77                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.55/0.77                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.55/0.77                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.77    (~( ![A:$i]:
% 0.55/0.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.77          ( ![B:$i]:
% 0.55/0.77            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.55/0.77              ( ![C:$i]:
% 0.55/0.77                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.55/0.77                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77                  ( ![D:$i]:
% 0.55/0.77                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.55/0.77                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77                      ( ( r1_subset_1 @ C @ D ) =>
% 0.55/0.77                        ( ![E:$i]:
% 0.55/0.77                          ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.77                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.55/0.77                              ( m1_subset_1 @
% 0.55/0.77                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.55/0.77                            ( ![F:$i]:
% 0.55/0.77                              ( ( ( v1_funct_1 @ F ) & 
% 0.55/0.77                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.55/0.77                                  ( m1_subset_1 @
% 0.55/0.77                                    F @ 
% 0.55/0.77                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.55/0.77                                ( ( ( k2_partfun1 @
% 0.55/0.77                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.55/0.77                                    ( k2_partfun1 @
% 0.55/0.77                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.55/0.77                                  ( ( k2_partfun1 @
% 0.55/0.77                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.55/0.77                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.55/0.77                                    ( E ) ) & 
% 0.55/0.77                                  ( ( k2_partfun1 @
% 0.55/0.77                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.55/0.77                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.55/0.77                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.55/0.77    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.55/0.77  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(t110_relat_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( v1_relat_1 @ A ) =>
% 0.55/0.77       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.55/0.77  thf('1', plain,
% 0.55/0.77      (![X12 : $i]:
% 0.55/0.77         (((k7_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.55/0.77  thf('2', plain,
% 0.55/0.77      (![X12 : $i]:
% 0.55/0.77         (((k7_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.55/0.77  thf('3', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('4', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('5', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(dt_k1_tmap_1, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.55/0.77         ( ~( v1_xboole_0 @ C ) ) & 
% 0.55/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.55/0.77         ( ~( v1_xboole_0 @ D ) ) & 
% 0.55/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.55/0.77         ( v1_funct_2 @ E @ C @ B ) & 
% 0.55/0.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.55/0.77         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.55/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.55/0.77       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.55/0.77         ( v1_funct_2 @
% 0.55/0.77           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.55/0.77           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.55/0.77         ( m1_subset_1 @
% 0.55/0.77           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.55/0.77           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.55/0.77  thf('6', plain,
% 0.55/0.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.55/0.77          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.55/0.77          | ~ (v1_funct_1 @ X29)
% 0.55/0.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.55/0.77          | (v1_xboole_0 @ X32)
% 0.55/0.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X33))
% 0.55/0.77          | (v1_xboole_0 @ X30)
% 0.55/0.77          | (v1_xboole_0 @ X31)
% 0.55/0.77          | (v1_xboole_0 @ X33)
% 0.55/0.77          | ~ (v1_funct_1 @ X34)
% 0.55/0.77          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.55/0.77          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.55/0.77          | (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X30 @ X32 @ X29 @ X34)))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.55/0.77  thf('7', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.55/0.77          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.55/0.77          | ~ (v1_funct_1 @ X0)
% 0.55/0.77          | (v1_xboole_0 @ X2)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.55/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.55/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.77  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('10', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.55/0.77          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.55/0.77          | ~ (v1_funct_1 @ X0)
% 0.55/0.77          | (v1_xboole_0 @ X2)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.55/0.77      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.55/0.77  thf('11', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_D)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.55/0.77          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.55/0.77          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['4', '10'])).
% 0.55/0.77  thf('12', plain, ((v1_funct_1 @ sk_F)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('13', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('14', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_D)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.55/0.77      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.55/0.77  thf('15', plain,
% 0.55/0.77      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.77  thf('16', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('17', plain,
% 0.55/0.77      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.55/0.77  thf('18', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('19', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('20', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('21', plain,
% 0.55/0.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.55/0.77          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.55/0.77          | ~ (v1_funct_1 @ X29)
% 0.55/0.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.55/0.77          | (v1_xboole_0 @ X32)
% 0.55/0.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X33))
% 0.55/0.77          | (v1_xboole_0 @ X30)
% 0.55/0.77          | (v1_xboole_0 @ X31)
% 0.55/0.77          | (v1_xboole_0 @ X33)
% 0.55/0.77          | ~ (v1_funct_1 @ X34)
% 0.55/0.77          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.55/0.77          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.55/0.77          | (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X30 @ X32 @ X29 @ X34) @ 
% 0.55/0.77             (k4_subset_1 @ X33 @ X30 @ X32) @ X31))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.55/0.77  thf('22', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.55/0.77           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.55/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.55/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.55/0.77          | ~ (v1_funct_1 @ X2)
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.55/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.77  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('24', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('25', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.55/0.77           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.55/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.55/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.55/0.77          | ~ (v1_funct_1 @ X2)
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.55/0.77      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.55/0.77  thf('26', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_D)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.55/0.77          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.55/0.77          | (v1_funct_2 @ 
% 0.55/0.77             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.55/0.77      inference('sup-', [status(thm)], ['19', '25'])).
% 0.55/0.77  thf('27', plain, ((v1_funct_1 @ sk_F)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('28', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('29', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_D)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | (v1_funct_2 @ 
% 0.55/0.77             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.55/0.77      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.55/0.77  thf('30', plain,
% 0.55/0.77      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['18', '29'])).
% 0.55/0.77  thf('31', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('32', plain,
% 0.55/0.77      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.77  thf('33', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('34', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('35', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('36', plain,
% 0.55/0.77      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.55/0.77          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.55/0.77          | ~ (v1_funct_1 @ X29)
% 0.55/0.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.55/0.77          | (v1_xboole_0 @ X32)
% 0.55/0.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X33))
% 0.55/0.77          | (v1_xboole_0 @ X30)
% 0.55/0.77          | (v1_xboole_0 @ X31)
% 0.55/0.77          | (v1_xboole_0 @ X33)
% 0.55/0.77          | ~ (v1_funct_1 @ X34)
% 0.55/0.77          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 0.55/0.77          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.55/0.77          | (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X30 @ X32 @ X29 @ X34) @ 
% 0.55/0.77             (k1_zfmisc_1 @ 
% 0.55/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X30 @ X32) @ X31))))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.55/0.77  thf('37', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.55/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.55/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.55/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.55/0.77          | ~ (v1_funct_1 @ X2)
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.55/0.77      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.77  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('39', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('40', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.77         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.55/0.77           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.55/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.55/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.55/0.77          | ~ (v1_funct_1 @ X2)
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.55/0.77      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.55/0.77  thf('41', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_D)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.55/0.77          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.55/0.77          | (m1_subset_1 @ 
% 0.55/0.77             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k1_zfmisc_1 @ 
% 0.55/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['34', '40'])).
% 0.55/0.77  thf('42', plain, ((v1_funct_1 @ sk_F)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('43', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('44', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_D)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.55/0.77          | (v1_xboole_0 @ sk_C)
% 0.55/0.77          | (v1_xboole_0 @ sk_B)
% 0.55/0.77          | (v1_xboole_0 @ X0)
% 0.55/0.77          | (m1_subset_1 @ 
% 0.55/0.77             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k1_zfmisc_1 @ 
% 0.55/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.55/0.77      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.55/0.77  thf('45', plain,
% 0.55/0.77      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77         (k1_zfmisc_1 @ 
% 0.55/0.77          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['33', '44'])).
% 0.55/0.77  thf('46', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('47', plain,
% 0.55/0.77      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77         (k1_zfmisc_1 @ 
% 0.55/0.77          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['45', '46'])).
% 0.55/0.77  thf(d1_tmap_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.55/0.77           ( ![C:$i]:
% 0.55/0.77             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.55/0.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77               ( ![D:$i]:
% 0.55/0.77                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.55/0.77                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77                   ( ![E:$i]:
% 0.55/0.77                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.55/0.77                         ( m1_subset_1 @
% 0.55/0.77                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.55/0.77                       ( ![F:$i]:
% 0.55/0.77                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.55/0.77                             ( m1_subset_1 @
% 0.55/0.77                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.55/0.77                           ( ( ( k2_partfun1 @
% 0.55/0.77                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.55/0.77                               ( k2_partfun1 @
% 0.55/0.77                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.55/0.77                             ( ![G:$i]:
% 0.55/0.77                               ( ( ( v1_funct_1 @ G ) & 
% 0.55/0.77                                   ( v1_funct_2 @
% 0.55/0.77                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.55/0.77                                   ( m1_subset_1 @
% 0.55/0.77                                     G @ 
% 0.55/0.77                                     ( k1_zfmisc_1 @
% 0.55/0.77                                       ( k2_zfmisc_1 @
% 0.55/0.77                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.55/0.77                                 ( ( ( G ) =
% 0.55/0.77                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.55/0.77                                   ( ( ( k2_partfun1 @
% 0.55/0.77                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.55/0.77                                         C ) =
% 0.55/0.77                                       ( E ) ) & 
% 0.55/0.77                                     ( ( k2_partfun1 @
% 0.55/0.77                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.55/0.77                                         D ) =
% 0.55/0.77                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.77  thf('48', plain,
% 0.55/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.77         ((v1_xboole_0 @ X22)
% 0.55/0.77          | (v1_xboole_0 @ X23)
% 0.55/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | ~ (v1_funct_1 @ X25)
% 0.55/0.77          | ~ (v1_funct_2 @ X25 @ X23 @ X22)
% 0.55/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.77          | ((X28) != (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25))
% 0.55/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22 @ X28 @ X27)
% 0.55/0.77              = (X26))
% 0.55/0.77          | ~ (m1_subset_1 @ X28 @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22)))
% 0.55/0.77          | ~ (v1_funct_2 @ X28 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22)
% 0.55/0.77          | ~ (v1_funct_1 @ X28)
% 0.55/0.77          | ((k2_partfun1 @ X27 @ X22 @ X26 @ (k9_subset_1 @ X24 @ X27 @ X23))
% 0.55/0.77              != (k2_partfun1 @ X23 @ X22 @ X25 @ 
% 0.55/0.77                  (k9_subset_1 @ X24 @ X27 @ X23)))
% 0.55/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X22)))
% 0.55/0.77          | ~ (v1_funct_2 @ X26 @ X27 @ X22)
% 0.55/0.77          | ~ (v1_funct_1 @ X26)
% 0.55/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | (v1_xboole_0 @ X27)
% 0.55/0.77          | (v1_xboole_0 @ X24))),
% 0.55/0.77      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.55/0.77  thf('49', plain,
% 0.55/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.77         ((v1_xboole_0 @ X24)
% 0.55/0.77          | (v1_xboole_0 @ X27)
% 0.55/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | ~ (v1_funct_1 @ X26)
% 0.55/0.77          | ~ (v1_funct_2 @ X26 @ X27 @ X22)
% 0.55/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X22)))
% 0.55/0.77          | ((k2_partfun1 @ X27 @ X22 @ X26 @ (k9_subset_1 @ X24 @ X27 @ X23))
% 0.55/0.77              != (k2_partfun1 @ X23 @ X22 @ X25 @ 
% 0.55/0.77                  (k9_subset_1 @ X24 @ X27 @ X23)))
% 0.55/0.77          | ~ (v1_funct_1 @ (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25))
% 0.55/0.77          | ~ (v1_funct_2 @ (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25) @ 
% 0.55/0.77               (k4_subset_1 @ X24 @ X27 @ X23) @ X22)
% 0.55/0.77          | ~ (m1_subset_1 @ (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25) @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22)))
% 0.55/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22 @ 
% 0.55/0.77              (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25) @ X27) = (
% 0.55/0.77              X26))
% 0.55/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.77          | ~ (v1_funct_2 @ X25 @ X23 @ X22)
% 0.55/0.77          | ~ (v1_funct_1 @ X25)
% 0.55/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | (v1_xboole_0 @ X23)
% 0.55/0.77          | (v1_xboole_0 @ X22))),
% 0.55/0.77      inference('simplify', [status(thm)], ['48'])).
% 0.55/0.77  thf('50', plain,
% 0.55/0.77      (((v1_xboole_0 @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_D)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | ~ (v1_funct_1 @ sk_F)
% 0.55/0.77        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77            = (sk_E))
% 0.55/0.77        | ~ (v1_funct_2 @ 
% 0.55/0.77             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.55/0.77        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.55/0.77        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.55/0.77        | ~ (v1_funct_1 @ sk_E)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['47', '49'])).
% 0.55/0.77  thf('51', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('52', plain, ((v1_funct_1 @ sk_F)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('53', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('54', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('55', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i]:
% 0.55/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.55/0.77  thf('56', plain,
% 0.55/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.55/0.77         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.55/0.77          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.55/0.77  thf('57', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.55/0.77  thf('58', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(redefinition_r1_subset_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.55/0.77       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.55/0.77  thf('59', plain,
% 0.55/0.77      (![X13 : $i, X14 : $i]:
% 0.55/0.77         ((v1_xboole_0 @ X13)
% 0.55/0.77          | (v1_xboole_0 @ X14)
% 0.55/0.77          | (r1_xboole_0 @ X13 @ X14)
% 0.55/0.77          | ~ (r1_subset_1 @ X13 @ X14))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.55/0.77  thf('60', plain,
% 0.55/0.77      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_C))),
% 0.55/0.77      inference('sup-', [status(thm)], ['58', '59'])).
% 0.55/0.77  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('62', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.77      inference('clc', [status(thm)], ['60', '61'])).
% 0.55/0.77  thf('63', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('64', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.55/0.77      inference('clc', [status(thm)], ['62', '63'])).
% 0.55/0.77  thf(t83_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.77  thf('65', plain,
% 0.55/0.77      (![X4 : $i, X5 : $i]:
% 0.55/0.77         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.55/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.55/0.77  thf('66', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.55/0.77      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.77  thf(t48_xboole_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.77  thf('67', plain,
% 0.55/0.77      (![X1 : $i, X2 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.55/0.77           = (k3_xboole_0 @ X1 @ X2))),
% 0.55/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.77  thf('68', plain,
% 0.55/0.77      (((k4_xboole_0 @ sk_C @ sk_C) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.77      inference('sup+', [status(thm)], ['66', '67'])).
% 0.55/0.77  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.55/0.77  thf('69', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.55/0.77      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.55/0.77  thf('70', plain,
% 0.55/0.77      (![X4 : $i, X5 : $i]:
% 0.55/0.77         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.55/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.55/0.77  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['69', '70'])).
% 0.55/0.77  thf('72', plain,
% 0.55/0.77      (![X1 : $i, X2 : $i]:
% 0.55/0.77         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.55/0.77           = (k3_xboole_0 @ X1 @ X2))),
% 0.55/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.77  thf('73', plain,
% 0.55/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.77      inference('sup+', [status(thm)], ['71', '72'])).
% 0.55/0.77  thf(t2_boole, axiom,
% 0.55/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.55/0.77  thf('74', plain,
% 0.55/0.77      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.77  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.77      inference('demod', [status(thm)], ['73', '74'])).
% 0.55/0.77  thf('76', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['68', '75'])).
% 0.55/0.77  thf('77', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(redefinition_k2_partfun1, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.77     ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.77       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.55/0.77  thf('78', plain,
% 0.55/0.77      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.55/0.77          | ~ (v1_funct_1 @ X18)
% 0.55/0.77          | ((k2_partfun1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.55/0.77  thf('79', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.55/0.77          | ~ (v1_funct_1 @ sk_E))),
% 0.55/0.77      inference('sup-', [status(thm)], ['77', '78'])).
% 0.55/0.77  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('81', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['79', '80'])).
% 0.55/0.77  thf('82', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.55/0.77  thf('83', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['68', '75'])).
% 0.55/0.77  thf('84', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('85', plain,
% 0.55/0.77      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.55/0.77          | ~ (v1_funct_1 @ X18)
% 0.55/0.77          | ((k2_partfun1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.55/0.77  thf('86', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.55/0.77          | ~ (v1_funct_1 @ sk_F))),
% 0.55/0.77      inference('sup-', [status(thm)], ['84', '85'])).
% 0.55/0.77  thf('87', plain, ((v1_funct_1 @ sk_F)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('88', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['86', '87'])).
% 0.55/0.77  thf('89', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('90', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('92', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('93', plain,
% 0.55/0.77      (((v1_xboole_0 @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_D)
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77            = (sk_E))
% 0.55/0.77        | ~ (v1_funct_2 @ 
% 0.55/0.77             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.55/0.77            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_A))),
% 0.55/0.77      inference('demod', [status(thm)],
% 0.55/0.77                ['50', '51', '52', '53', '54', '57', '76', '81', '82', '83', 
% 0.55/0.77                 '88', '89', '90', '91', '92'])).
% 0.55/0.77  thf('94', plain,
% 0.55/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.55/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | ~ (v1_funct_2 @ 
% 0.55/0.77             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77            = (sk_E))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('simplify', [status(thm)], ['93'])).
% 0.55/0.77  thf('95', plain,
% 0.55/0.77      (((v1_xboole_0 @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77            = (sk_E))
% 0.55/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.55/0.77            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['32', '94'])).
% 0.55/0.77  thf('96', plain,
% 0.55/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.55/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77            = (sk_E))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('simplify', [status(thm)], ['95'])).
% 0.55/0.77  thf('97', plain,
% 0.55/0.77      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77            != (sk_E))
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.55/0.77            != (sk_F)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('98', plain,
% 0.55/0.77      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77          != (sk_E)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.55/0.77                = (sk_E))))),
% 0.55/0.77      inference('split', [status(esa)], ['97'])).
% 0.55/0.77  thf('99', plain,
% 0.55/0.77      (![X12 : $i]:
% 0.55/0.77         (((k7_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.55/0.77  thf('100', plain,
% 0.55/0.77      (![X12 : $i]:
% 0.55/0.77         (((k7_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.55/0.77  thf('101', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['86', '87'])).
% 0.55/0.77  thf('102', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.55/0.77  thf('103', plain,
% 0.55/0.77      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('split', [status(esa)], ['97'])).
% 0.55/0.77  thf('104', plain,
% 0.55/0.77      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['102', '103'])).
% 0.55/0.77  thf('105', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.55/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.55/0.77  thf('106', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['68', '75'])).
% 0.55/0.77  thf('107', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['68', '75'])).
% 0.55/0.77  thf('108', plain,
% 0.55/0.77      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.55/0.77          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.55/0.77  thf('109', plain,
% 0.55/0.77      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.55/0.77          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['101', '108'])).
% 0.55/0.77  thf('110', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.55/0.77      inference('demod', [status(thm)], ['79', '80'])).
% 0.55/0.77  thf('111', plain,
% 0.55/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['109', '110'])).
% 0.55/0.77  thf('112', plain,
% 0.55/0.77      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.55/0.77         | ~ (v1_relat_1 @ sk_F)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['100', '111'])).
% 0.55/0.77  thf('113', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(cc1_relset_1, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i]:
% 0.55/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.77       ( v1_relat_1 @ C ) ))).
% 0.55/0.77  thf('114', plain,
% 0.55/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.77         ((v1_relat_1 @ X15)
% 0.55/0.77          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.55/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.77  thf('115', plain, ((v1_relat_1 @ sk_F)),
% 0.55/0.77      inference('sup-', [status(thm)], ['113', '114'])).
% 0.55/0.77  thf('116', plain,
% 0.55/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['112', '115'])).
% 0.55/0.77  thf('117', plain,
% 0.55/0.77      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['99', '116'])).
% 0.55/0.77  thf('118', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('119', plain,
% 0.55/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.55/0.77         ((v1_relat_1 @ X15)
% 0.55/0.77          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.55/0.77      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.77  thf('120', plain, ((v1_relat_1 @ sk_E)),
% 0.55/0.77      inference('sup-', [status(thm)], ['118', '119'])).
% 0.55/0.77  thf('121', plain,
% 0.55/0.77      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.55/0.77         <= (~
% 0.55/0.77             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['117', '120'])).
% 0.55/0.77  thf('122', plain,
% 0.55/0.77      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.55/0.77      inference('simplify', [status(thm)], ['121'])).
% 0.55/0.77  thf('123', plain,
% 0.55/0.77      (![X12 : $i]:
% 0.55/0.77         (((k7_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.55/0.77  thf('124', plain,
% 0.55/0.77      (![X12 : $i]:
% 0.55/0.77         (((k7_relat_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))
% 0.55/0.77          | ~ (v1_relat_1 @ X12))),
% 0.55/0.77      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.55/0.77  thf('125', plain,
% 0.55/0.77      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['15', '16'])).
% 0.55/0.77  thf('126', plain,
% 0.55/0.77      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.77  thf('127', plain,
% 0.55/0.77      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77         (k1_zfmisc_1 @ 
% 0.55/0.77          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_D))),
% 0.55/0.77      inference('demod', [status(thm)], ['45', '46'])).
% 0.55/0.77  thf('128', plain,
% 0.55/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.77         ((v1_xboole_0 @ X22)
% 0.55/0.77          | (v1_xboole_0 @ X23)
% 0.55/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | ~ (v1_funct_1 @ X25)
% 0.55/0.77          | ~ (v1_funct_2 @ X25 @ X23 @ X22)
% 0.55/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.77          | ((X28) != (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25))
% 0.55/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22 @ X28 @ X23)
% 0.55/0.77              = (X25))
% 0.55/0.77          | ~ (m1_subset_1 @ X28 @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22)))
% 0.55/0.77          | ~ (v1_funct_2 @ X28 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22)
% 0.55/0.77          | ~ (v1_funct_1 @ X28)
% 0.55/0.77          | ((k2_partfun1 @ X27 @ X22 @ X26 @ (k9_subset_1 @ X24 @ X27 @ X23))
% 0.55/0.77              != (k2_partfun1 @ X23 @ X22 @ X25 @ 
% 0.55/0.77                  (k9_subset_1 @ X24 @ X27 @ X23)))
% 0.55/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X22)))
% 0.55/0.77          | ~ (v1_funct_2 @ X26 @ X27 @ X22)
% 0.55/0.77          | ~ (v1_funct_1 @ X26)
% 0.55/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | (v1_xboole_0 @ X27)
% 0.55/0.77          | (v1_xboole_0 @ X24))),
% 0.55/0.77      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.55/0.77  thf('129', plain,
% 0.55/0.77      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.77         ((v1_xboole_0 @ X24)
% 0.55/0.77          | (v1_xboole_0 @ X27)
% 0.55/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | ~ (v1_funct_1 @ X26)
% 0.55/0.77          | ~ (v1_funct_2 @ X26 @ X27 @ X22)
% 0.55/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X22)))
% 0.55/0.77          | ((k2_partfun1 @ X27 @ X22 @ X26 @ (k9_subset_1 @ X24 @ X27 @ X23))
% 0.55/0.77              != (k2_partfun1 @ X23 @ X22 @ X25 @ 
% 0.55/0.77                  (k9_subset_1 @ X24 @ X27 @ X23)))
% 0.55/0.77          | ~ (v1_funct_1 @ (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25))
% 0.55/0.77          | ~ (v1_funct_2 @ (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25) @ 
% 0.55/0.77               (k4_subset_1 @ X24 @ X27 @ X23) @ X22)
% 0.55/0.77          | ~ (m1_subset_1 @ (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25) @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22)))
% 0.55/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X24 @ X27 @ X23) @ X22 @ 
% 0.55/0.77              (k1_tmap_1 @ X24 @ X22 @ X27 @ X23 @ X26 @ X25) @ X23) = (
% 0.55/0.77              X25))
% 0.55/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.55/0.77          | ~ (v1_funct_2 @ X25 @ X23 @ X22)
% 0.55/0.77          | ~ (v1_funct_1 @ X25)
% 0.55/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.55/0.77          | (v1_xboole_0 @ X23)
% 0.55/0.77          | (v1_xboole_0 @ X22))),
% 0.55/0.77      inference('simplify', [status(thm)], ['128'])).
% 0.55/0.77  thf('130', plain,
% 0.55/0.77      (((v1_xboole_0 @ sk_D)
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ sk_B)
% 0.55/0.77        | (v1_xboole_0 @ sk_D)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | ~ (v1_funct_1 @ sk_F)
% 0.55/0.77        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.55/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.55/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.55/0.77            = (sk_F))
% 0.55/0.77        | ~ (v1_funct_2 @ 
% 0.55/0.77             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.55/0.77             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.55/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.55/0.77        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.55/0.77            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.55/0.77            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.55/0.77                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.55/0.77        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.55/0.77        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.55/0.77        | ~ (v1_funct_1 @ sk_E)
% 0.55/0.77        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.77        | (v1_xboole_0 @ sk_C)
% 0.55/0.77        | (v1_xboole_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['127', '129'])).
% 0.55/0.77  thf('131', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('132', plain, ((v1_funct_1 @ sk_F)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('133', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('134', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('135', plain,
% 0.61/0.77      (![X0 : $i]:
% 0.61/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.61/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.61/0.77  thf('136', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.77      inference('demod', [status(thm)], ['68', '75'])).
% 0.61/0.77  thf('137', plain,
% 0.61/0.77      (![X0 : $i]:
% 0.61/0.77         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.61/0.77      inference('demod', [status(thm)], ['79', '80'])).
% 0.61/0.77  thf('138', plain,
% 0.61/0.77      (![X0 : $i]:
% 0.61/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.61/0.77      inference('sup-', [status(thm)], ['55', '56'])).
% 0.61/0.77  thf('139', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D))),
% 0.61/0.77      inference('demod', [status(thm)], ['68', '75'])).
% 0.61/0.77  thf('140', plain,
% 0.61/0.77      (![X0 : $i]:
% 0.61/0.77         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.61/0.77      inference('demod', [status(thm)], ['86', '87'])).
% 0.61/0.77  thf('141', plain,
% 0.61/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('142', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('143', plain, ((v1_funct_1 @ sk_E)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('144', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('145', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | ~ (v1_funct_2 @ 
% 0.61/0.77             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.61/0.77             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.61/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.61/0.77        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.61/0.77            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_A))),
% 0.61/0.77      inference('demod', [status(thm)],
% 0.61/0.77                ['130', '131', '132', '133', '134', '135', '136', '137', 
% 0.61/0.77                 '138', '139', '140', '141', '142', '143', '144'])).
% 0.61/0.77  thf('146', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.61/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.61/0.77        | ~ (v1_funct_2 @ 
% 0.61/0.77             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.61/0.77             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('simplify', [status(thm)], ['145'])).
% 0.61/0.77  thf('147', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.61/0.77        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.61/0.77            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['126', '146'])).
% 0.61/0.77  thf('148', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.61/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('simplify', [status(thm)], ['147'])).
% 0.61/0.77  thf('149', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.61/0.77            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['125', '148'])).
% 0.61/0.77  thf('150', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('simplify', [status(thm)], ['149'])).
% 0.61/0.77  thf('151', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_F)
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['124', '150'])).
% 0.61/0.77  thf('152', plain, ((v1_relat_1 @ sk_F)),
% 0.61/0.77      inference('sup-', [status(thm)], ['113', '114'])).
% 0.61/0.77  thf('153', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F)))),
% 0.61/0.77      inference('demod', [status(thm)], ['151', '152'])).
% 0.61/0.77  thf('154', plain,
% 0.61/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_E)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('sup-', [status(thm)], ['123', '153'])).
% 0.61/0.77  thf('155', plain, ((v1_relat_1 @ sk_E)),
% 0.61/0.77      inference('sup-', [status(thm)], ['118', '119'])).
% 0.61/0.77  thf('156', plain,
% 0.61/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('demod', [status(thm)], ['154', '155'])).
% 0.61/0.77  thf('157', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77            = (sk_F)))),
% 0.61/0.77      inference('simplify', [status(thm)], ['156'])).
% 0.61/0.77  thf('158', plain,
% 0.61/0.77      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77          != (sk_F)))
% 0.61/0.77         <= (~
% 0.61/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77                = (sk_F))))),
% 0.61/0.77      inference('split', [status(esa)], ['97'])).
% 0.61/0.77  thf('159', plain,
% 0.61/0.77      (((((sk_F) != (sk_F))
% 0.61/0.77         | (v1_xboole_0 @ sk_A)
% 0.61/0.77         | (v1_xboole_0 @ sk_B)
% 0.61/0.77         | (v1_xboole_0 @ sk_C)
% 0.61/0.77         | (v1_xboole_0 @ sk_D)))
% 0.61/0.77         <= (~
% 0.61/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77                = (sk_F))))),
% 0.61/0.77      inference('sup-', [status(thm)], ['157', '158'])).
% 0.61/0.77  thf('160', plain,
% 0.61/0.77      ((((v1_xboole_0 @ sk_D)
% 0.61/0.77         | (v1_xboole_0 @ sk_C)
% 0.61/0.77         | (v1_xboole_0 @ sk_B)
% 0.61/0.77         | (v1_xboole_0 @ sk_A)))
% 0.61/0.77         <= (~
% 0.61/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77                = (sk_F))))),
% 0.61/0.77      inference('simplify', [status(thm)], ['159'])).
% 0.61/0.77  thf('161', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('162', plain,
% 0.61/0.77      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C)))
% 0.61/0.77         <= (~
% 0.61/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77                = (sk_F))))),
% 0.61/0.77      inference('sup-', [status(thm)], ['160', '161'])).
% 0.61/0.77  thf('163', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('164', plain,
% 0.61/0.77      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B)))
% 0.61/0.77         <= (~
% 0.61/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77                = (sk_F))))),
% 0.61/0.77      inference('clc', [status(thm)], ['162', '163'])).
% 0.61/0.77  thf('165', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('166', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_B))
% 0.61/0.77         <= (~
% 0.61/0.77             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77                = (sk_F))))),
% 0.61/0.77      inference('clc', [status(thm)], ['164', '165'])).
% 0.61/0.77  thf('167', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('168', plain,
% 0.61/0.77      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77          = (sk_F)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['166', '167'])).
% 0.61/0.77  thf('169', plain,
% 0.61/0.77      (~
% 0.61/0.77       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.61/0.77          = (sk_E))) | 
% 0.61/0.77       ~
% 0.61/0.77       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.61/0.77          = (sk_F))) | 
% 0.61/0.77       ~
% 0.61/0.77       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.61/0.77          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.61/0.77             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.61/0.77      inference('split', [status(esa)], ['97'])).
% 0.61/0.77  thf('170', plain,
% 0.61/0.77      (~
% 0.61/0.77       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.61/0.77          = (sk_E)))),
% 0.61/0.77      inference('sat_resolution*', [status(thm)], ['122', '168', '169'])).
% 0.61/0.77  thf('171', plain,
% 0.61/0.77      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.61/0.77         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.61/0.77         != (sk_E))),
% 0.61/0.77      inference('simpl_trail', [status(thm)], ['98', '170'])).
% 0.61/0.77  thf('172', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.61/0.77        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('simplify_reflect-', [status(thm)], ['96', '171'])).
% 0.61/0.77  thf('173', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.61/0.77            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.61/0.77      inference('sup-', [status(thm)], ['17', '172'])).
% 0.61/0.77  thf('174', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('simplify', [status(thm)], ['173'])).
% 0.61/0.77  thf('175', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_F)
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A))),
% 0.61/0.77      inference('sup-', [status(thm)], ['2', '174'])).
% 0.61/0.77  thf('176', plain, ((v1_relat_1 @ sk_F)),
% 0.61/0.77      inference('sup-', [status(thm)], ['113', '114'])).
% 0.61/0.77  thf('177', plain,
% 0.61/0.77      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | (v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A))),
% 0.61/0.77      inference('demod', [status(thm)], ['175', '176'])).
% 0.61/0.77  thf('178', plain,
% 0.61/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | ~ (v1_relat_1 @ sk_E)
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('sup-', [status(thm)], ['1', '177'])).
% 0.61/0.77  thf('179', plain, ((v1_relat_1 @ sk_E)),
% 0.61/0.77      inference('sup-', [status(thm)], ['118', '119'])).
% 0.61/0.77  thf('180', plain,
% 0.61/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.61/0.77        | (v1_xboole_0 @ sk_A)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_D))),
% 0.61/0.77      inference('demod', [status(thm)], ['178', '179'])).
% 0.61/0.77  thf('181', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_D)
% 0.61/0.77        | (v1_xboole_0 @ sk_C)
% 0.61/0.77        | (v1_xboole_0 @ sk_B)
% 0.61/0.77        | (v1_xboole_0 @ sk_A))),
% 0.61/0.77      inference('simplify', [status(thm)], ['180'])).
% 0.61/0.77  thf('182', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('183', plain,
% 0.61/0.77      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.61/0.77      inference('sup-', [status(thm)], ['181', '182'])).
% 0.61/0.77  thf('184', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('185', plain, (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.61/0.77      inference('clc', [status(thm)], ['183', '184'])).
% 0.61/0.77  thf('186', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.61/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.77  thf('187', plain, ((v1_xboole_0 @ sk_B)),
% 0.61/0.77      inference('clc', [status(thm)], ['185', '186'])).
% 0.61/0.77  thf('188', plain, ($false), inference('demod', [status(thm)], ['0', '187'])).
% 0.61/0.77  
% 0.61/0.77  % SZS output end Refutation
% 0.61/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
