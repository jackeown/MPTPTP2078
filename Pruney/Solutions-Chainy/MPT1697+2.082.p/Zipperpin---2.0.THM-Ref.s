%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yeFgYjLnBw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:06 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 618 expanded)
%              Number of leaves         :   32 ( 190 expanded)
%              Depth                    :   36
%              Number of atoms          : 3735 (27512 expanded)
%              Number of equality atoms :  136 ( 889 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29 ) @ ( k4_subset_1 @ X28 @ X25 @ X27 ) @ X26 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X28 @ X25 @ X27 ) @ X26 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ( X23
       != ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 @ X23 @ X22 )
        = X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k2_partfun1 @ X22 @ X17 @ X21 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) )
       != ( k2_partfun1 @ X18 @ X17 @ X20 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X17 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X17 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X17 ) ) )
      | ( ( k2_partfun1 @ X22 @ X17 @ X21 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) )
       != ( k2_partfun1 @ X18 @ X17 @ X20 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) @ X22 )
        = X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X17 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_subset_1 @ X11 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k2_partfun1 @ X14 @ X15 @ X13 @ X16 )
        = ( k7_relat_1 @ X13 @ X16 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k2_partfun1 @ X14 @ X15 @ X13 @ X16 )
        = ( k7_relat_1 @ X13 @ X16 ) ) ) ),
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','86'])).

thf('88',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E ) ),
    inference('sup-',[status(thm)],['2','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) )
    | ( v1_relat_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('94',plain,(
    v1_relat_1 @ sk_F ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('99',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('102',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['96'])).

thf('103',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('105',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('106',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('107',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('110',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['99','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_F ),
    inference(demod,[status(thm)],['92','93'])).

thf('113',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['98','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('119',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['114','119'])).

thf('121',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('123',plain,(
    ! [X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('124',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('125',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('126',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('127',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ( X23
       != ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 @ X23 @ X18 )
        = X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k2_partfun1 @ X22 @ X17 @ X21 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) )
       != ( k2_partfun1 @ X18 @ X17 @ X20 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X17 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('128',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X17 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X17 ) ) )
      | ( ( k2_partfun1 @ X22 @ X17 @ X21 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) )
       != ( k2_partfun1 @ X18 @ X17 @ X20 @ ( k9_subset_1 @ X19 @ X22 @ X18 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X19 @ X22 @ X18 ) @ X17 @ ( k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20 ) @ X18 )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
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
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('135',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('140',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
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
    inference(demod,[status(thm)],['129','130','131','132','133','134','135','136','137','138','139','140','141','142','143'])).

thf('145',plain,
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
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
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
    inference('sup-',[status(thm)],['125','145'])).

thf('147',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
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
    inference('sup-',[status(thm)],['124','147'])).

thf('149',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['123','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_F ),
    inference(demod,[status(thm)],['92','93'])).

thf('152',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['122','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['117','118'])).

thf('155',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['96'])).

thf('158',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
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
    inference(split,[status(esa)],['96'])).

thf('169',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['121','167','168'])).

thf('170',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['97','169'])).

thf('171',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['95','170'])).

thf('172',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['117','118'])).

thf('174',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['0','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yeFgYjLnBw
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 140 iterations in 0.146s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.60  thf(t6_tmap_1, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.60           ( ![C:$i]:
% 0.42/0.60             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.60                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.60               ( ![D:$i]:
% 0.42/0.60                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.60                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.60                   ( ( r1_subset_1 @ C @ D ) =>
% 0.42/0.60                     ( ![E:$i]:
% 0.42/0.60                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.60                           ( m1_subset_1 @
% 0.42/0.60                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.60                         ( ![F:$i]:
% 0.42/0.60                           ( ( ( v1_funct_1 @ F ) & 
% 0.42/0.60                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.60                               ( m1_subset_1 @
% 0.42/0.60                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.60                             ( ( ( k2_partfun1 @
% 0.42/0.60                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.60                                 ( k2_partfun1 @
% 0.42/0.60                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.42/0.60                               ( ( k2_partfun1 @
% 0.42/0.60                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.60                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.42/0.60                                 ( E ) ) & 
% 0.42/0.60                               ( ( k2_partfun1 @
% 0.42/0.60                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.60                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.42/0.60                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.60              ( ![C:$i]:
% 0.42/0.60                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.60                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.60                  ( ![D:$i]:
% 0.42/0.60                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.60                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.60                      ( ( r1_subset_1 @ C @ D ) =>
% 0.42/0.60                        ( ![E:$i]:
% 0.42/0.60                          ( ( ( v1_funct_1 @ E ) & 
% 0.42/0.60                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.60                              ( m1_subset_1 @
% 0.42/0.60                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.60                            ( ![F:$i]:
% 0.42/0.60                              ( ( ( v1_funct_1 @ F ) & 
% 0.42/0.60                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.60                                  ( m1_subset_1 @
% 0.42/0.60                                    F @ 
% 0.42/0.60                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.60                                ( ( ( k2_partfun1 @
% 0.42/0.60                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.60                                    ( k2_partfun1 @
% 0.42/0.60                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.42/0.60                                  ( ( k2_partfun1 @
% 0.42/0.60                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.60                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.42/0.60                                    ( E ) ) & 
% 0.42/0.60                                  ( ( k2_partfun1 @
% 0.42/0.60                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.60                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.42/0.60                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.42/0.60  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t110_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X10 : $i]:
% 0.42/0.60         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_relat_1 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X10 : $i]:
% 0.42/0.60         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.60          | ~ (v1_relat_1 @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.42/0.60  thf('3', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(dt_k1_tmap_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.42/0.60         ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.42/0.60         ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.42/0.60         ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.42/0.60         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.60       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.42/0.60         ( v1_funct_2 @
% 0.42/0.60           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.60           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.42/0.60         ( m1_subset_1 @
% 0.42/0.60           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.60          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.42/0.60          | ~ (v1_funct_1 @ X24)
% 0.42/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.42/0.60          | (v1_xboole_0 @ X27)
% 0.42/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X28))
% 0.42/0.60          | (v1_xboole_0 @ X25)
% 0.42/0.60          | (v1_xboole_0 @ X26)
% 0.42/0.60          | (v1_xboole_0 @ X28)
% 0.42/0.60          | ~ (v1_funct_1 @ X29)
% 0.42/0.60          | ~ (v1_funct_2 @ X29 @ X27 @ X26)
% 0.42/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.42/0.60          | (v1_funct_1 @ (k1_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29)))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.42/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | (v1_xboole_0 @ X2)
% 0.42/0.60          | (v1_xboole_0 @ sk_B)
% 0.42/0.60          | (v1_xboole_0 @ sk_C)
% 0.42/0.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.42/0.60          | (v1_xboole_0 @ X1)
% 0.42/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.42/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.60          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.60  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.42/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.42/0.60          | ~ (v1_funct_1 @ X0)
% 0.42/0.60          | (v1_xboole_0 @ X2)
% 0.42/0.60          | (v1_xboole_0 @ sk_B)
% 0.42/0.60          | (v1_xboole_0 @ sk_C)
% 0.42/0.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.42/0.60          | (v1_xboole_0 @ X1)
% 0.42/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.42/0.60      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.60          | (v1_xboole_0 @ sk_D)
% 0.42/0.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.60          | (v1_xboole_0 @ sk_C)
% 0.42/0.60          | (v1_xboole_0 @ sk_B)
% 0.42/0.60          | (v1_xboole_0 @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.60          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.60          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '10'])).
% 0.42/0.60  thf('12', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('13', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.60          | (v1_xboole_0 @ sk_D)
% 0.42/0.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.60          | (v1_xboole_0 @ sk_C)
% 0.42/0.60          | (v1_xboole_0 @ sk_B)
% 0.42/0.60          | (v1_xboole_0 @ X0)
% 0.42/0.60          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.60      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.60        | (v1_xboole_0 @ sk_A)
% 0.42/0.60        | (v1_xboole_0 @ sk_B)
% 0.42/0.60        | (v1_xboole_0 @ sk_C)
% 0.42/0.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.60        | (v1_xboole_0 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['3', '14'])).
% 0.42/0.60  thf('16', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.60        | (v1_xboole_0 @ sk_A)
% 0.42/0.60        | (v1_xboole_0 @ sk_B)
% 0.42/0.60        | (v1_xboole_0 @ sk_C)
% 0.42/0.60        | (v1_xboole_0 @ sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('18', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.60          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.42/0.60          | ~ (v1_funct_1 @ X24)
% 0.42/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.42/0.60          | (v1_xboole_0 @ X27)
% 0.42/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X28))
% 0.42/0.60          | (v1_xboole_0 @ X25)
% 0.42/0.60          | (v1_xboole_0 @ X26)
% 0.42/0.60          | (v1_xboole_0 @ X28)
% 0.42/0.60          | ~ (v1_funct_1 @ X29)
% 0.42/0.60          | ~ (v1_funct_2 @ X29 @ X27 @ X26)
% 0.42/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.42/0.60          | (v1_funct_2 @ (k1_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29) @ 
% 0.42/0.60             (k4_subset_1 @ X28 @ X25 @ X27) @ X26))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.60           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.42/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.60          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.60          | ~ (v1_funct_1 @ X2)
% 0.42/0.60          | (v1_xboole_0 @ X1)
% 0.42/0.60          | (v1_xboole_0 @ sk_B)
% 0.42/0.60          | (v1_xboole_0 @ sk_C)
% 0.42/0.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.60          | (v1_xboole_0 @ X0)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.60          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('24', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.60           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.42/0.60          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.60          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.60          | ~ (v1_funct_1 @ X2)
% 0.42/0.60          | (v1_xboole_0 @ X1)
% 0.42/0.60          | (v1_xboole_0 @ sk_B)
% 0.42/0.60          | (v1_xboole_0 @ sk_C)
% 0.42/0.60          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.60          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.42/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.42/0.61  thf('26', plain,
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
% 0.42/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.42/0.61  thf('27', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('28', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('29', plain,
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
% 0.42/0.61      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['18', '29'])).
% 0.42/0.61  thf('31', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.61  thf('33', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.61          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.42/0.61          | ~ (v1_funct_1 @ X24)
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.42/0.61          | (v1_xboole_0 @ X27)
% 0.42/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X28))
% 0.42/0.61          | (v1_xboole_0 @ X25)
% 0.42/0.61          | (v1_xboole_0 @ X26)
% 0.42/0.61          | (v1_xboole_0 @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X29)
% 0.42/0.61          | ~ (v1_funct_2 @ X29 @ X27 @ X26)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.42/0.61          | (m1_subset_1 @ (k1_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X28 @ X25 @ X27) @ X26))))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('37', plain,
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
% 0.42/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.61  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('39', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('40', plain,
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
% 0.42/0.61      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.42/0.61  thf('41', plain,
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
% 0.42/0.61      inference('sup-', [status(thm)], ['34', '40'])).
% 0.42/0.61  thf('42', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('43', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('44', plain,
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
% 0.42/0.61      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '44'])).
% 0.42/0.61  thf('46', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['45', '46'])).
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
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X17)
% 0.42/0.61          | (v1_xboole_0 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ~ (v1_funct_2 @ X20 @ X18 @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.42/0.61          | ((X23) != (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17 @ X23 @ X22)
% 0.42/0.61              = (X21))
% 0.42/0.61          | ~ (m1_subset_1 @ X23 @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17)))
% 0.42/0.61          | ~ (v1_funct_2 @ X23 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17)
% 0.42/0.61          | ~ (v1_funct_1 @ X23)
% 0.42/0.61          | ((k2_partfun1 @ X22 @ X17 @ X21 @ (k9_subset_1 @ X19 @ X22 @ X18))
% 0.42/0.61              != (k2_partfun1 @ X18 @ X17 @ X20 @ 
% 0.42/0.61                  (k9_subset_1 @ X19 @ X22 @ X18)))
% 0.42/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X17)))
% 0.42/0.61          | ~ (v1_funct_2 @ X21 @ X22 @ X17)
% 0.42/0.61          | ~ (v1_funct_1 @ X21)
% 0.42/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | (v1_xboole_0 @ X22)
% 0.42/0.61          | (v1_xboole_0 @ X19))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X19)
% 0.42/0.61          | (v1_xboole_0 @ X22)
% 0.42/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | ~ (v1_funct_1 @ X21)
% 0.42/0.61          | ~ (v1_funct_2 @ X21 @ X22 @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X17)))
% 0.42/0.61          | ((k2_partfun1 @ X22 @ X17 @ X21 @ (k9_subset_1 @ X19 @ X22 @ X18))
% 0.42/0.61              != (k2_partfun1 @ X18 @ X17 @ X20 @ 
% 0.42/0.61                  (k9_subset_1 @ X19 @ X22 @ X18)))
% 0.42/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20))
% 0.42/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20) @ 
% 0.42/0.61               (k4_subset_1 @ X19 @ X22 @ X18) @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20) @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17)))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17 @ 
% 0.42/0.61              (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20) @ X22) = (
% 0.42/0.61              X21))
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.42/0.61          | ~ (v1_funct_2 @ X20 @ X18 @ X17)
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | (v1_xboole_0 @ X18)
% 0.42/0.61          | (v1_xboole_0 @ X17))),
% 0.42/0.61      inference('simplify', [status(thm)], ['48'])).
% 0.42/0.61  thf('50', plain,
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
% 0.42/0.61      inference('sup-', [status(thm)], ['47', '49'])).
% 0.42/0.61  thf('51', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('52', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('53', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('55', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 0.42/0.61          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('58', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_r1_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.42/0.61       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      (![X11 : $i, X12 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X11)
% 0.42/0.61          | (v1_xboole_0 @ X12)
% 0.42/0.61          | (r1_xboole_0 @ X11 @ X12)
% 0.42/0.61          | ~ (r1_subset_1 @ X11 @ X12))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.42/0.61  thf('60', plain,
% 0.42/0.61      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.42/0.61  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('62', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.42/0.61      inference('clc', [status(thm)], ['60', '61'])).
% 0.42/0.61  thf('63', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('64', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.42/0.61      inference('clc', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf(d7_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.42/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.42/0.61  thf('66', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k2_partfun1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.42/0.61  thf('68', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.42/0.61          | ~ (v1_funct_1 @ X13)
% 0.42/0.61          | ((k2_partfun1 @ X14 @ X15 @ X13 @ X16) = (k7_relat_1 @ X13 @ X16)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.42/0.61  thf('69', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E))),
% 0.42/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('71', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['69', '70'])).
% 0.42/0.61  thf('72', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('73', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('74', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('75', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.42/0.61          | ~ (v1_funct_1 @ X13)
% 0.42/0.61          | ((k2_partfun1 @ X14 @ X15 @ X13 @ X16) = (k7_relat_1 @ X13 @ X16)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.42/0.61  thf('76', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F))),
% 0.42/0.61      inference('sup-', [status(thm)], ['74', '75'])).
% 0.42/0.61  thf('77', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('78', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['76', '77'])).
% 0.42/0.61  thf('79', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('80', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('81', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('82', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('83', plain,
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
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['50', '51', '52', '53', '54', '57', '66', '71', '72', '73', 
% 0.42/0.61                 '78', '79', '80', '81', '82'])).
% 0.42/0.61  thf('84', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
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
% 0.42/0.61      inference('simplify', [status(thm)], ['83'])).
% 0.42/0.61  thf('85', plain,
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
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['32', '84'])).
% 0.42/0.61  thf('86', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['85'])).
% 0.42/0.61  thf('87', plain,
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
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['17', '86'])).
% 0.42/0.61  thf('88', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['87'])).
% 0.42/0.61  thf('89', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_F)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '88'])).
% 0.42/0.61  thf('90', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc2_relat_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_relat_1 @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.61  thf('91', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.42/0.61          | (v1_relat_1 @ X6)
% 0.42/0.61          | ~ (v1_relat_1 @ X7))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.61  thf('92', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)) | (v1_relat_1 @ sk_F))),
% 0.42/0.61      inference('sup-', [status(thm)], ['90', '91'])).
% 0.42/0.61  thf(fc6_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.61  thf('93', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.61  thf('94', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('demod', [status(thm)], ['92', '93'])).
% 0.42/0.61  thf('95', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E)))),
% 0.42/0.61      inference('demod', [status(thm)], ['89', '94'])).
% 0.42/0.61  thf('96', plain,
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
% 0.42/0.61  thf('97', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          != (sk_E)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61                = (sk_E))))),
% 0.42/0.61      inference('split', [status(esa)], ['96'])).
% 0.42/0.61  thf('98', plain,
% 0.42/0.61      (![X10 : $i]:
% 0.42/0.61         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.42/0.61  thf('99', plain,
% 0.42/0.61      (![X10 : $i]:
% 0.42/0.61         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.42/0.61  thf('100', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['76', '77'])).
% 0.42/0.61  thf('101', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('102', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('split', [status(esa)], ['96'])).
% 0.42/0.61  thf('103', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['101', '102'])).
% 0.42/0.61  thf('104', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('105', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('106', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('107', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.42/0.61  thf('108', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0)
% 0.42/0.61          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['100', '107'])).
% 0.42/0.61  thf('109', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['69', '70'])).
% 0.42/0.61  thf('110', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['108', '109'])).
% 0.42/0.61  thf('111', plain,
% 0.42/0.61      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61         | ~ (v1_relat_1 @ sk_F)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['99', '110'])).
% 0.42/0.61  thf('112', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('demod', [status(thm)], ['92', '93'])).
% 0.42/0.61  thf('113', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['111', '112'])).
% 0.42/0.61  thf('114', plain,
% 0.42/0.61      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['98', '113'])).
% 0.42/0.61  thf('115', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('116', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.42/0.61          | (v1_relat_1 @ X6)
% 0.42/0.61          | ~ (v1_relat_1 @ X7))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.61  thf('117', plain,
% 0.42/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)) | (v1_relat_1 @ sk_E))),
% 0.42/0.61      inference('sup-', [status(thm)], ['115', '116'])).
% 0.42/0.61  thf('118', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.61  thf('119', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('demod', [status(thm)], ['117', '118'])).
% 0.42/0.61  thf('120', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['114', '119'])).
% 0.42/0.61  thf('121', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['120'])).
% 0.42/0.61  thf('122', plain,
% 0.42/0.61      (![X10 : $i]:
% 0.42/0.61         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.42/0.61  thf('123', plain,
% 0.42/0.61      (![X10 : $i]:
% 0.42/0.61         (((k7_relat_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))
% 0.42/0.61          | ~ (v1_relat_1 @ X10))),
% 0.42/0.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.42/0.61  thf('124', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.42/0.61  thf('125', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.61  thf('126', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.42/0.61  thf('127', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X17)
% 0.42/0.61          | (v1_xboole_0 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ~ (v1_funct_2 @ X20 @ X18 @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.42/0.61          | ((X23) != (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17 @ X23 @ X18)
% 0.42/0.61              = (X20))
% 0.42/0.61          | ~ (m1_subset_1 @ X23 @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17)))
% 0.42/0.61          | ~ (v1_funct_2 @ X23 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17)
% 0.42/0.61          | ~ (v1_funct_1 @ X23)
% 0.42/0.61          | ((k2_partfun1 @ X22 @ X17 @ X21 @ (k9_subset_1 @ X19 @ X22 @ X18))
% 0.42/0.61              != (k2_partfun1 @ X18 @ X17 @ X20 @ 
% 0.42/0.61                  (k9_subset_1 @ X19 @ X22 @ X18)))
% 0.42/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X17)))
% 0.42/0.61          | ~ (v1_funct_2 @ X21 @ X22 @ X17)
% 0.42/0.61          | ~ (v1_funct_1 @ X21)
% 0.42/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | (v1_xboole_0 @ X22)
% 0.42/0.61          | (v1_xboole_0 @ X19))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.42/0.61  thf('128', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X19)
% 0.42/0.61          | (v1_xboole_0 @ X22)
% 0.42/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | ~ (v1_funct_1 @ X21)
% 0.42/0.61          | ~ (v1_funct_2 @ X21 @ X22 @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X17)))
% 0.42/0.61          | ((k2_partfun1 @ X22 @ X17 @ X21 @ (k9_subset_1 @ X19 @ X22 @ X18))
% 0.42/0.61              != (k2_partfun1 @ X18 @ X17 @ X20 @ 
% 0.42/0.61                  (k9_subset_1 @ X19 @ X22 @ X18)))
% 0.42/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20))
% 0.42/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20) @ 
% 0.42/0.61               (k4_subset_1 @ X19 @ X22 @ X18) @ X17)
% 0.42/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20) @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17)))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X19 @ X22 @ X18) @ X17 @ 
% 0.42/0.61              (k1_tmap_1 @ X19 @ X17 @ X22 @ X18 @ X21 @ X20) @ X18) = (
% 0.42/0.61              X20))
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.42/0.61          | ~ (v1_funct_2 @ X20 @ X18 @ X17)
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.42/0.61          | (v1_xboole_0 @ X18)
% 0.42/0.61          | (v1_xboole_0 @ X17))),
% 0.42/0.61      inference('simplify', [status(thm)], ['127'])).
% 0.42/0.61  thf('129', plain,
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
% 0.42/0.61      inference('sup-', [status(thm)], ['126', '128'])).
% 0.42/0.61  thf('130', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('131', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('132', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('133', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('134', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('135', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('136', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['69', '70'])).
% 0.42/0.61  thf('137', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('138', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('139', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['76', '77'])).
% 0.42/0.61  thf('140', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('141', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('142', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('143', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('144', plain,
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
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['129', '130', '131', '132', '133', '134', '135', '136', 
% 0.42/0.61                 '137', '138', '139', '140', '141', '142', '143'])).
% 0.42/0.61  thf('145', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
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
% 0.42/0.61      inference('simplify', [status(thm)], ['144'])).
% 0.42/0.61  thf('146', plain,
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
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['125', '145'])).
% 0.42/0.61  thf('147', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['146'])).
% 0.42/0.61  thf('148', plain,
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
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['124', '147'])).
% 0.42/0.61  thf('149', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['148'])).
% 0.42/0.61  thf('150', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_F)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['123', '149'])).
% 0.42/0.61  thf('151', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('demod', [status(thm)], ['92', '93'])).
% 0.42/0.61  thf('152', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('demod', [status(thm)], ['150', '151'])).
% 0.42/0.61  thf('153', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_E)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['122', '152'])).
% 0.42/0.61  thf('154', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('demod', [status(thm)], ['117', '118'])).
% 0.42/0.61  thf('155', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['153', '154'])).
% 0.42/0.61  thf('156', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['155'])).
% 0.42/0.61  thf('157', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          != (sk_F)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('split', [status(esa)], ['96'])).
% 0.42/0.61  thf('158', plain,
% 0.42/0.61      (((((sk_F) != (sk_F))
% 0.42/0.61         | (v1_xboole_0 @ sk_A)
% 0.42/0.61         | (v1_xboole_0 @ sk_B)
% 0.42/0.61         | (v1_xboole_0 @ sk_C)
% 0.42/0.61         | (v1_xboole_0 @ sk_D)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['156', '157'])).
% 0.42/0.61  thf('159', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_D)
% 0.42/0.61         | (v1_xboole_0 @ sk_C)
% 0.42/0.61         | (v1_xboole_0 @ sk_B)
% 0.42/0.61         | (v1_xboole_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['158'])).
% 0.42/0.61  thf('160', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('161', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['159', '160'])).
% 0.42/0.61  thf('162', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('163', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('clc', [status(thm)], ['161', '162'])).
% 0.42/0.61  thf('164', plain, (~ (v1_xboole_0 @ sk_C)),
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
% 0.42/0.61      inference('split', [status(esa)], ['96'])).
% 0.42/0.61  thf('169', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          = (sk_E)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['121', '167', '168'])).
% 0.42/0.61  thf('170', plain,
% 0.42/0.61      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61         != (sk_E))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['97', '169'])).
% 0.42/0.61  thf('171', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['95', '170'])).
% 0.42/0.61  thf('172', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_E)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '171'])).
% 0.42/0.61  thf('173', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('demod', [status(thm)], ['117', '118'])).
% 0.42/0.61  thf('174', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['172', '173'])).
% 0.42/0.61  thf('175', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('simplify', [status(thm)], ['174'])).
% 0.42/0.61  thf('176', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('177', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['175', '176'])).
% 0.42/0.61  thf('178', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('179', plain, (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.42/0.61      inference('clc', [status(thm)], ['177', '178'])).
% 0.42/0.61  thf('180', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('181', plain, ((v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('clc', [status(thm)], ['179', '180'])).
% 0.42/0.61  thf('182', plain, ($false), inference('demod', [status(thm)], ['0', '181'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
